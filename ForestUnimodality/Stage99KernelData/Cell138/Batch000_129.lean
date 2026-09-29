import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell138.Parameters
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch000_049
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch050_099
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree000.table
  base := (5569233033275745186173821761/100000000000000000000000000)
  polynomial :=
    { denominator := 15052000000000000000000000000000000000000000
      center := (95549)
      previous := (0)
      next := (85075)
      square := (2218944305354789156559114328000000000000000)
      linear := (-10250250045978713802075077367920000000000000)
      constant := (838280956168665165422883651465720000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree000.table
  base := (5569233033275745186173821761/100000000000000000000000000)
  polynomial :=
    { denominator := 7526000000000000000000000000000000000000000
      center := (47787)
      previous := (0)
      next := (42525)
      square := (1109472152677394578279557164000000000000000)
      linear := (-5125125022989356901037538683960000000000000)
      constant := (419140478084332582711441825732860000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree001.table
  base := (66888394977679526395231798119435464179243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-426651934344290381254901700816623640000000000000)
      constant := (17253384585640845193151838149740146228937489097206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree001.table
  base := (334384005444465543135993899266014241792663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-118520204707542522889790122920402400000000000000)
      constant := (4791802376093268209524172389457154707690971040047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12478764629742241649/25000000000000000000)
  directionHi := (49915058518968966597/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree002.table
  base := (209905855704835192314941228911181900779401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-2530793251907098310874633782069503200000000000000)
      constant := (55758405879727718279689871285745153960995897817842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree002.table
  base := (8393646418422569028792673486002857945819/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-28122236421508059137311791100419480000000000000)
      constant := (619362408414914891023560908499031974978949417055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12478764629742241649/25000000000000000000)
  centralHi := (49915058518968966597/100000000000000000000)
  directionLo := (17647638181043152003/25000000000000000000)
  directionHi := (70590552724172608013/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree003.table
  base := (138606606023427392441241823663103736366803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-325369648010304968386084340006209800000000000000)
      constant := (4336595214251114116302384605876157374220752939414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree003.table
  base := (13855132615881932228982558794295761672531/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-32540431901507613696665557616758480000000000000)
      constant := (433516477933091196535485073073280070033523235478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/25000000000000000000)
  centralHi := (70590552724172608013/100000000000000000000)
  directionLo := (43227708708813983399/50000000000000000000)
  directionHi := (86455417417627966799/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree004.table
  base := (96453671236497598137868767817368727008229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-3325860412278391120074884338042273200000000000000)
      constant := (29939502231929415185254773798808989375524966552618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree004.table
  base := (48205216107105367700287553632463943008707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-184793136907535841280096620665487400000000000000)
      constant := (1662795709475743283979064749441188738819319182966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/50000000000000000000)
  centralHi := (86455417417627966799/100000000000000000000)
  directionLo := (99830117037937933193/100000000000000000000)
  directionHi := (49915058518968966597/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree005.table
  base := (17608328793260837995804558071218212440191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-3723393992464037524675009616028658200000000000000)
      constant := (25171861127685344158195947846436950561482500564088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree005.table
  base := (70400325126804301892470390284612673548919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-206884114307533614076865453247182400000000000000)
      constant := (1398112747878427119809283454751515244494522807311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/100000000000000000000)
  centralHi := (49915058518968966597/50000000000000000000)
  directionLo := (55806731974647292603/50000000000000000000)
  directionHi := (111613463949294585207/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree006.table
  base := (26744922377819397986454608279426053223959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-457880841405520436586126099335004800000000000000)
      constant := (2547561900059463305325367206622416721617017156284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree006.table
  base := (13366112847970223726214195355105573187169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-228975091707531386873634285828877400000000000000)
      constant := (1273611514689142356288772107625276616688726686244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55806731974647292603/50000000000000000000)
  centralHi := (111613463949294585207/100000000000000000000)
  directionLo := (15283302981579572087/12500000000000000000)
  directionHi := (122266423852636576697/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree007.table
  base := (20888592967290741453881367625270318586923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-4518461152835330333875260172001428200000000000000)
      constant := (22227791096933473017480725139941194178738151319532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree007.table
  base := (41757077884474577703504358860214269146511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-251066069107529159670403118410572400000000000000)
      constant := (1234835778929473210017526930345749164826081520359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15283302981579572087/12500000000000000000)
  centralHi := (122266423852636576697/100000000000000000000)
  directionLo := (26412566303685580969/20000000000000000000)
  directionHi := (66031415759213952423/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree008.table
  base := (16590938281359181955380550758002733130363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-4915994733020976738475385449987813200000000000000)
      constant := (22532377455662033229504256776870265529162208008492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree008.table
  base := (6633070101852378994290369493525525305989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-54631409301505386493434390198453480000000000000)
      constant := (250373433907459488808685540105312684146580952141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26412566303685580969/20000000000000000000)
  centralHi := (66031415759213952423/50000000000000000000)
  directionLo := (17647638181043152003/12500000000000000000)
  directionHi := (5647244217933808641/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree009.table
  base := (1697822465870546960648179399921220349/640000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-118078406960147180957233571732759960000000000000)
      constant := (523160362180981433913652059748439213925493631250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree009.table
  base := (26514378683054537543763647380286930109687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-295248023907524705263940783573962400000000000000)
      constant := (1308069037298160041766737450000106486344356457103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/12500000000000000000)
  centralHi := (5647244217933808641/4000000000000000000)
  directionLo := (149745175556906899789/100000000000000000000)
  directionHi := (14974517555690689979/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree010.table
  base := (21151532677169389957924971084449115298619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-5711061893392269547675636005960583200000000000000)
      constant := (25087695281755342216533205100358458276520749118998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree010.table
  base := (1056956122372868661154239654476365218741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-63467800261504495612141923231131480000000000000)
      constant := (278804860801886592499113702834902552012378108916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149745175556906899789/100000000000000000000)
  centralHi := (14974517555690689979/10000000000000000000)
  directionLo := (157845274460532913511/100000000000000000000)
  directionHi := (19730659307566614189/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree011.table
  base := (16664610203268152017199269903679704550263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-6108595473577915952275761283946968200000000000000)
      constant := (27070318345977219201154511549055791070682275340046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree011.table
  base := (16653426132784181054641755330508068429847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-339429978707520250857478448737352400000000000000)
      constant := (1504264940128051140538986361933192442330198164143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157845274460532913511/100000000000000000000)
  centralHi := (19730659307566614189/12500000000000000000)
  directionLo := (165549520496052964121/100000000000000000000)
  directionHi := (82774760248026482061/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree012.table
  base := (641767676040188734975270684820479067847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-144580645639190274597241923598518960000000000000)
      constant := (654019158210721712932181938174005266093407889144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree012.table
  base := (6412557514825146650890143669779947431929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-361520956107518023654247281319047400000000000000)
      constant := (1635503312531601794737119364534884796894461272002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165549520496052964121/100000000000000000000)
  centralHi := (82774760248026482061/50000000000000000000)
  directionLo := (43227708708813983399/25000000000000000000)
  directionHi := (172910834835255933597/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree013.table
  base := (9517682081920083462748337341508878041089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-6903662633949208761476011839919738200000000000000)
      constant := (32132093147856507513142084855420116836369765312738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree013.table
  base := (1188527449768709305219794761382697806969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-383611933507515796451016113900742400000000000000)
      constant := (1785672467866163217967937019253550284480883342088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/25000000000000000000)
  centralHi := (172910834835255933597/100000000000000000000)
  directionLo := (35994260581585644383/20000000000000000000)
  directionHi := (44992825726982055479/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree014.table
  base := (3307402844876228868693563897932569744551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-7301196214134855166076137117906123200000000000000)
      constant := (35149341251286677141795844001939450949736643608284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree014.table
  base := (1651503870542692417602200482923337779741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-405702910907513569247784946482437400000000000000)
      constant := (1953402772902779611351670356187185408020869344916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35994260581585644383/20000000000000000000)
  centralHi := (44992825726982055479/25000000000000000000)
  directionLo := (93382523709376892261/50000000000000000000)
  directionHi := (186765047418753784523/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree015.table
  base := (1014725840485587153925921897017066714167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-855414421591166841186251377321389800000000000000)
      constant := (4273924445719778965289388743935858365705035313784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree015.table
  base := (4050719385886462670942741474713690125461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-427793888307511342044553779064132400000000000000)
      constant := (2137734404717162013059931334219252016290158962909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382523709376892261/50000000000000000000)
  centralHi := (186765047418753784523/100000000000000000000)
  directionLo := (4833004759223386467/2500000000000000000)
  directionHi := (193320190368935458681/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree016.table
  base := (899917751023546005224847220379749052647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-8096263374506147975276387673878893200000000000000)
      constant := (42067249695564549549426043144420370867470571024348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree016.table
  base := (358442494890531241949837992002353236913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-89976973141501822968264522329165480000000000000)
      constant := (467591534427566983522471180113963650232385118297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4833004759223386467/2500000000000000000)
  centralHi := (193320190368935458681/100000000000000000000)
  directionLo := (99830117037937933193/50000000000000000000)
  directionHi := (199660234075875866387/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree017.table
  base := (-100613613120845130952109291560378540001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-8493796954691794379876512951865278200000000000000)
      constant := (45945233364189173245756078007680416763356052873916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree017.table
  base := (-104161826107741200425254402644586756263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-471975843107506887638091444227522400000000000000)
      constant := (2553522900059287479814690065854852696692308223106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/50000000000000000000)
  centralHi := (199660234075875866387/100000000000000000000)
  directionLo := (205805058582595677863/100000000000000000000)
  directionHi := (25725632322824459733/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree018.table
  base := (-1975483198143411167512973554692201513089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-987925614986382309386293136650184800000000000000)
      constant := (5565702120063388931369643744938103642185208095918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree018.table
  base := (-9910409591540087129223401665752456599/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-98813364101500932086972055361843480000000000000)
      constant := (556797678280676840310767671559594188095719790760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805058582595677863/100000000000000000000)
  centralHi := (25725632322824459733/12500000000000000000)
  directionLo := (52942914543129456009/25000000000000000000)
  directionHi := (211771658172517824037/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree019.table
  base := (-221793284608112084786682662264105586163/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-9288864115063087189076763507838048200000000000000)
      constant := (54498941021844704191872273745892367653883303234464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree019.table
  base := (-3554819923155602522000645017110201219767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-516157797907502433231629109390912400000000000000)
      constant := (3028989414210568740169507525949528196604093139377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52942914543129456009/25000000000000000000)
  centralHi := (211771658172517824037/100000000000000000000)
  directionLo := (217574695845104725947/100000000000000000000)
  directionHi := (54393673961276181487/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree020.table
  base := (-2471269200132785183654550046022630135373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-9686397695248733593676888785824433200000000000000)
      constant := (59162572531672137090861003175361613060510515910668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree020.table
  base := (-4948219662234973824091153478517142907199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-538248775307500206028397941972607400000000000000)
      constant := (3288218947760633276424908644916369887036910843369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217574695845104725947/100000000000000000000)
  centralHi := (54393673961276181487/25000000000000000000)
  directionLo := (223226927898589170413/100000000000000000000)
  directionHi := (111613463949294585207/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree021.table
  base := (-6175514203391491259865862817766983039071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1120436808381597777586334895978979800000000000000)
      constant := (7119722215474795831074893587887148216343242074002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree021.table
  base := (-3090387048341061310674705883107085316241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-560339752707497978825166774554302400000000000000)
      constant := (3561415128598581741681971636635058941149217990542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223226927898589170413/100000000000000000000)
  centralHi := (111613463949294585207/50000000000000000000)
  directionLo := (228739533981325634129/100000000000000000000)
  directionHi := (22873953398132563413/10000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree022.table
  base := (-3631767039290250034518168229172801609599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-10481464855620026402877139341797203200000000000000)
      constant := (69239667006485297114031133740078931139165820959684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree022.table
  base := (-3634198505626014067077867064757175219851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-582430730107495751621935607135997400000000000000)
      constant := (3848352614842854006588623007062214209848595370362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228739533981325634129/100000000000000000000)
  centralHi := (22873953398132563413/10000000000000000000)
  directionLo := (117061188564940387879/50000000000000000000)
  directionHi := (234122377129880775759/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree023.table
  base := (-1644075055517644000184752103961042828039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-2175799687161134561495452923956717640000000000000)
      constant := (14929112429094133582110978174259081280747136785362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree023.table
  base := (-8224865289757544744604034185236767606249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-604521707507493524418704439717692400000000000000)
      constant := (4148836323490366688722022365512276203181788703919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117061188564940387879/50000000000000000000)
  centralHi := (234122377129880775759/100000000000000000000)
  directionLo := (239384211133270477681/100000000000000000000)
  directionHi := (119692105566635238841/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree024.table
  base := (-9058014515136718763532917986984884796843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1252948001776813245786376655307774800000000000000)
      constant := (8921348077194194229699898538545348661662344907066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree024.table
  base := (-9062155154257741970167042011708485098211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-626612684907491297215473272299387400000000000000)
      constant := (4462696669212781835732007401184750472275350642341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384211133270477681/100000000000000000000)
  centralHi := (119692105566635238841/50000000000000000000)
  directionLo := (244532847705273153393/100000000000000000000)
  directionHi := (122266423852636576697/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree025.table
  base := (-4893446829764246599008997877868675137737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-11674065596176965616677515175756358200000000000000)
      constant := (86176717199159433813194951719865643490017648888092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree025.table
  base := (-305959619805736915604117963162541945779/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-648703662307489070012242104881082400000000000000)
      constant := (4789785802442453326709110396047958898001776747168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244532847705273153393/100000000000000000000)
  centralHi := (122266423852636576697/50000000000000000000)
  directionLo := (124787646297422416491/50000000000000000000)
  directionHi := (249575292594844832983/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree026.table
  base := (-10416135870430013842276328333638203761183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-12071599176362612021277640453742743200000000000000)
      constant := (92296990320017283432139836587185483772933835441314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree026.table
  base := (-2083929142540558306606989472059409115699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-134158927941497368561802187492555480000000000000)
      constant := (1025994909735010232737180022197102468881561606869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124787646297422416491/50000000000000000000)
  centralHi := (249575292594844832983/100000000000000000000)
  directionLo := (254517857410348530797/100000000000000000000)
  directionHi := (127258928705174265399/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree027.table
  base := (-2190745037092344509016463807101335107691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-277091839034405742797283682927313960000000000000)
      constant := (2192242601367225694762978168005592215748924480442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree027.table
  base := (-1369618992738397697904462522289611320377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-692885617107484615605779770044472400000000000000)
      constant := (5483149865144794831753328994724268431573188290296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254517857410348530797/100000000000000000000)
  centralHi := (127258928705174265399/50000000000000000000)
  directionLo := (129683126126441950197/50000000000000000000)
  directionHi := (51873250450576780079/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree028.table
  base := (-356458061048236002698980568183703762983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-12866666336733904830477891009715513200000000000000)
      constant := (105236714172987446428393060225215793042049470902848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree028.table
  base := (-11409621900872957693808772396723811059799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-714976594507482388402548602626167400000000000000)
      constant := (5849212696096082119019275526473400489069177053969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129683126126441950197/50000000000000000000)
  centralHi := (51873250450576780079/20000000000000000000)
  directionLo := (264125663036855809691/100000000000000000000)
  directionHi := (66031415759213952423/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree029.table
  base := (-11781071824617218654602667198368656739527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-13264199916919551235078016287701898200000000000000)
      constant := (112052817271516278179498789628644126664025556598866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree029.table
  base := (-1472974026901019509538295930512004912137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-737067571907480161199317435207862400000000000000)
      constant := (6228076145873213504970040753361861318822479430776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264125663036855809691/100000000000000000000)
  centralHi := (66031415759213952423/25000000000000000000)
  directionLo := (268800816482410997431/100000000000000000000)
  directionHi := (33600102060301374679/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree030.table
  base := (-12082356382573335542761753234981974413347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1517970388567244182186460173965364800000000000000)
      constant := (13233094738174944200699162861083570435706661248714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree030.table
  base := (-12084851414241053521034339634681416154827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-759158549307477933996086267789557400000000000000)
      constant := (6619663911990239133776116216610522386088319514237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268800816482410997431/100000000000000000000)
  centralHi := (33600102060301374679/12500000000000000000)
  directionLo := (273396035100297115029/100000000000000000000)
  directionHi := (27339603510029711503/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree031.table
  base := (-12315248486941030467397182245221002752161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-14059267077290844044278266843674668200000000000000)
      constant := (126370612943995794548772661923066299587488832246238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree031.table
  base := (-3079383823353206297917437007091294539817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-781249526707475706792855100371252400000000000000)
      constant := (7023908934783362535561232098508427621049656203708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273396035100297115029/100000000000000000000)
  centralHi := (27339603510029711503/10000000000000000000)
  directionLo := (138957641995245253007/50000000000000000000)
  directionHi := (55583056798098101203/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree032.table
  base := (-6241957357172836345256560852761562854303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-14456800657476490448878392121661053200000000000000)
      constant := (133870036183055168195066460925514799918042097140548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree032.table
  base := (-1560751171556170216694773672324287631463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-803340504107473479589623932952947400000000000000)
      constant := (7440752229789292265111775685620916514670993622024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138957641995245253007/50000000000000000000)
  centralHi := (55583056798098101203/20000000000000000000)
  directionLo := (17647638181043152003/6250000000000000000)
  directionHi := (282362210896690432049/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree033.table
  base := (-6296011410905323725702048294068394811867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1650481581962459650386501933294159800000000000000)
      constant := (15732798612409464605582730699802887258870960297908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree033.table
  base := (-12593940371719967291334299695259129169959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-825431481507471252386392765534642400000000000000)
      constant := (7870141875627923233327320088794456119660550836929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/6250000000000000000)
  centralHi := (282362210896690432049/100000000000000000000)
  directionLo := (57348036133565787997/20000000000000000000)
  directionHi := (143370090333914469993/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree034.table
  base := (-12642803811583678984525121864327038280957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-15251867817847783258078642677633823200000000000000)
      constant := (149545243402204225523851992613168278875099229168806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree034.table
  base := (-12644558286938705798844904890503114295013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-847522458907469025183161598116337400000000000000)
      constant := (8312032135014075019227789432999516006556300062803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57348036133565787997/20000000000000000000)
  centralHi := (143370090333914469993/50000000000000000000)
  directionLo := (291052305052496153173/100000000000000000000)
  directionHi := (145526152526248076587/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree035.table
  base := (-12639105916194498871915456163629122395243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-15649401398033429662678767955620208200000000000000)
      constant := (157719477888440799074815071067420984805360137830794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree035.table
  base := (-12640710381419015991036038049608256075863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-869613436307466797979930430698032400000000000000)
      constant := (8766382690218041830355201683868911647670503099153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291052305052496153173/100000000000000000000)
  centralHi := (145526152526248076587/50000000000000000000)
  directionLo := (7382536714407664147/2500000000000000000)
  directionHi := (295301468576306565881/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree036.table
  base := (-12583441616532310823889911684794069543499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1782992775357675118586543692622954800000000000000)
      constant := (18457472286846988332943453950011970290132602617338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree036.table
  base := (-12584908209145956326217068256482272111627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-891704413707464570776699263279727400000000000000)
      constant := (9233157977210942615465016720891134581395374815037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7382536714407664147/2500000000000000000)
  centralHi := (295301468576306565881/100000000000000000000)
  directionLo := (299490351113813799579/100000000000000000000)
  directionHi := (14974517555690689979/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree037.table
  base := (-12478028638950946514269355267543913461767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-16444468558404722471879018511592978200000000000000)
      constant := (174737996220911125103500621758043243899530076344786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree037.table
  base := (-3119842153774402937990099897016287306299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-913795391107462343573468095861422400000000000000)
      constant := (9712326605093240890403253162600425591461005581876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299490351113813799579/100000000000000000000)
  centralHi := (14974517555690689979/5000000000000000000)
  directionLo := (151810723828413688737/50000000000000000000)
  directionHi := (12144857906273095099/4000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree038.table
  base := (-3081206434939845443450114199915039685987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-16842002138590368876479143789579363200000000000000)
      constant := (183581215552538920944198491338859970148139634670184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree038.table
  base := (-3081512380384353970306941171442626019147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-935886368507460116370236928443117400000000000000)
      constant := (10203860849354797572690092284261551467060324976628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151810723828413688737/50000000000000000000)
  centralHi := (12144857906273095099/4000000000000000000)
  directionLo := (307697085693348196509/100000000000000000000)
  directionHi := (30769708569334819651/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree039.table
  base := (-6062781985170424357797275592464612528193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-1915503968752890586786585451951749800000000000000)
      constant := (21405163040095985112200309907511116821575079421532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree039.table
  base := (-2425336238765299028424879271880593397631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-191595469181491577833401152204962480000000000000)
      constant := (2141547241829136853214639527900666757169260840361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307697085693348196509/100000000000000000000)
  centralHi := (30769708569334819651/10000000000000000000)
  directionLo := (155859720270450055589/50000000000000000000)
  directionHi := (311719440540900111179/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree040.table
  base := (-237635480379956550824523605655369774791/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-3527413859792332337135878869110426640000000000000)
      constant := (40386672299879014066078284565075770081664150057780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree040.table
  base := (-1485349197763283096044984695835443869841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-980068323307455661963774593606507400000000000000)
      constant := (11223931020113336956944067036724923148904299494968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155859720270450055589/50000000000000000000)
  centralHi := (311719440540900111179/100000000000000000000)
  directionLo := (315690548921065827023/100000000000000000000)
  directionHi := (19730659307566614189/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree041.table
  base := (-181168908486315405229255742822717086653/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-18034602879147308090279519623538518200000000000000)
      constant := (211441552790888333918526833917798371425154368740736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree041.table
  base := (-5797870126329645804969483837848964355617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1002159300707453434760543426188202400000000000000)
      constant := (11752426115530441796952835432469893223998974361454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315690548921065827023/100000000000000000000)
  centralHi := (19730659307566614189/6250000000000000000)
  directionLo := (319612321015689181781/100000000000000000000)
  directionHi := (159806160507844590891/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree042.table
  base := (-11265871134944764757289677286764262137863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2048015162148106054986627211280544800000000000000)
      constant := (24574526187059407043055617898024856644935117242306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree042.table
  base := (-88021244940282341621477503253489302397/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1024250278107451207557312258769897400000000000000)
      constant := (12293204529434824777874842225741756129710895988096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319612321015689181781/100000000000000000000)
  centralHi := (159806160507844590891/50000000000000000000)
  directionLo := (323486551207292154117/100000000000000000000)
  directionHi := (161743275603646077059/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree043.table
  base := (-2179203740772953597980573796608137504679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-3765934007903720179895954035902257640000000000000)
      constant := (46224127913122228067209895991615407307103127246482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree043.table
  base := (-10896791989365037753099413784387328350597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1046341255507448980354081091351592400000000000000)
      constant := (12846251236355496501851616079490650006597055229107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323486551207292154117/100000000000000000000)
  centralHi := (161743275603646077059/50000000000000000000)
  directionLo := (65462985535015173311/20000000000000000000)
  directionHi := (81828731918768966639/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree044.table
  base := (-10486193606849450385531168742764845887129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-19227203619704247304079895457497673200000000000000)
      constant := (241291024654120677944419091509119281389627371833582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree044.table
  base := (-10486898361652071265630109844833395159507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1068432232907446753150849923933287400000000000000)
      constant := (13411552922930363740815484025067448447697598923317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65462985535015173311/20000000000000000000)
  centralHi := (81828731918768966639/25000000000000000000)
  directionLo := (165549520496052964121/50000000000000000000)
  directionHi := (331099040992105928243/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree045.table
  base := (-5018614906953759458383625627901755517191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2180526355543321523186668970609339800000000000000)
      constant := (27964630931583391134772040464831199387169572138884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree045.table
  base := (-10037871920430129773672575259250553550953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1090523210307444525947618756514982400000000000000)
      constant := (13989097787349398724347314968744831035874955408943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165549520496052964121/50000000000000000000)
  centralHi := (331099040992105928243/100000000000000000000)
  directionLo := (16742019592394187781/5000000000000000000)
  directionHi := (334840391847883755621/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree046.table
  base := (-4774933478799084064962490970928948716959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-20022270780075540113280146013470443200000000000000)
      constant := (262292412236204017390603010076209523545318986181444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree046.table
  base := (-596903238596441498431418876346180255479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1112614187707442298744387589096677400000000000000)
      constant := (14578875363097575864957250372663425661247266944784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16742019592394187781/5000000000000000000)
  centralHi := (334840391847883755621/100000000000000000000)
  directionLo := (169270199001327781443/50000000000000000000)
  directionHi := (338540398002655562887/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree047.table
  base := (-9024761282615206459569162659548787858331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-20419804360261186517880271291456828200000000000000)
      constant := (273123058944337315225015894543452949534505929677098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree047.table
  base := (-9025293852890204740431820962678977594793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1134705165107440071541156421678372400000000000000)
      constant := (15180876363937490454523436574441636722010517599983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169270199001327781443/50000000000000000000)
  centralHi := (338540398002655562887/100000000000000000000)
  directionLo := (342200400564856924069/100000000000000000000)
  directionHi := (34220040056485692407/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree048.table
  base := (-8462495283157435478949731775386048402949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2313037548938536991386710729938134800000000000000)
      constant := (31574830004528563979826965274226947428744124123238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree048.table
  base := (-4231490054820051506086985155643835919349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1156796142507437844337925254260067400000000000000)
      constant := (15795092547473103756223261609289789159147495580038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342200400564856924069/100000000000000000000)
  centralHi := (34220040056485692407/10000000000000000000)
  directionLo := (43227708708813983399/12500000000000000000)
  directionHi := (345821669670511867193/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree049.table
  base := (-1572717238264839610481386289548572177897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-4242974304126495865416104369485919640000000000000)
      constant := (59088702738354479723083870921127090632791047477326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree049.table
  base := (-7864027440502445973632830423939471621267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1178887119907435617134694086841762400000000000000)
      constant := (16421516594982698491601179351236807723572155285877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/12500000000000000000)
  centralHi := (345821669670511867193/100000000000000000000)
  directionLo := (13976216385311310647/4000000000000000000)
  directionHi := (10918919051024461443/3125000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree050.table
  base := (-289139738345117738193351957456304416503/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-4322481020163625146336129425083196640000000000000)
      constant := (61386614558196827808778092878967504116218401789370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree050.table
  base := (-7228894947172294872075468454293771520229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1200978097307433389931462919423457400000000000000)
      constant := (17060142005508684406930537341252526419626170441299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13976216385311310647/4000000000000000000)
  centralHi := (10918919051024461443/3125000000000000000)
  directionLo := (17647638181043152003/5000000000000000000)
  directionHi := (352952763620863040061/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree051.table
  base := (-6557625354422508943773822819317397871473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2445548742333752459586752489266929800000000000000)
      constant := (35404671475273048409920043891067985194249404082126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree051.table
  base := (-1639497644190365652698940700208929508771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1223069074707431162728231752005152400000000000000)
      constant := (17710963002451015169604313604548946228886862630804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/5000000000000000000)
  centralHi := (352952763620863040061/100000000000000000000)
  directionLo := (356464817919744944719/100000000000000000000)
  directionHi := (4455810223996811809/1250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree052.table
  base := (-5851344789206170652378802993732680833259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-22407472261189418540880897681388753200000000000000)
      constant := (330570332651460514195015418674369458774403851306122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree052.table
  base := (-5851676943187296159664080483566331612731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1245160052107428935525000584586847400000000000000)
      constant := (18373974451135339394497505836030826321653686488461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356464817919744944719/100000000000000000000)
  centralHi := (4455810223996811809/1250000000000000000)
  directionLo := (359942605815856443831/100000000000000000000)
  directionHi := (44992825726982055479/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree053.table
  base := (-5109974457030230179556339589083149847679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (305279055)
      previous := (0)
      next := (271814625)
      square := (7089527055608551355206370277960000000000000000)
      linear := (-430283129082548395197755150176889400000000000000)
      constant := (6466374691768904594443518912475503083153429053594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree053.table
  base := (-5110276467756968566804486442007496136181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16964385)
      previous := (0)
      next := (15096375)
      square := (393862614200475075289242793220000000000000000)
      linear := (-23910396783158994496637158814500800000000000000)
      constant := (359418335585310534157291172512972868734808113687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359942605815856443831/100000000000000000000)
  centralHi := (44992825726982055479/12500000000000000000)
  directionLo := (363387111147961753721/100000000000000000000)
  directionHi := (181693555573980876861/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree054.table
  base := (-4333801379334290967966048243032358095501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2578059935728967927786794248595724800000000000000)
      constant := (39453838684159342030668321186203336048798375400662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree054.table
  base := (-433407592127273554836904143714604158197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-257868401381484896223707649950047480000000000000)
      constant := (3947310189277269542119832663189062254703655489414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363387111147961753721/100000000000000000000)
  centralHi := (181693555573980876861/50000000000000000000)
  directionLo := (36679927155790973009/10000000000000000000)
  directionHi := (366799271557909730091/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree055.table
  base := (-3523080922187803782750919573911876614953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-23600073001746357754681273515347908200000000000000)
      constant := (367670336044026313312251710604476730079702116672974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree055.table
  base := (-440416304954959364960077717088017505327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1311432984307422253915307082331932400000000000000)
      constant := (20436108319462473725462576636787038811496890237896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36679927155790973009/10000000000000000000)
  centralHi := (366799271557909730091/100000000000000000000)
  directionLo := (92544995367917283139/25000000000000000000)
  directionHi := (370179981471669132557/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree056.table
  base := (-2678040349929089795367944307277878242051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-23997606581932004159281398793334293200000000000000)
      constant := (380475164397702759196863000778846235854360428800858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree056.table
  base := (-267826707596723880736146699882451720659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-266704792341484005342415182982725480000000000000)
      constant := (4229568138027886907463258358598988287002255537258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92544995367917283139/25000000000000000000)
  centralHi := (370179981471669132557/100000000000000000000)
  directionLo := (93382523709376892261/25000000000000000000)
  directionHi := (74706018967501513809/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree057.table
  base := (-1798881970373569983796155715198257213383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2710571129124183395986836007924519800000000000000)
      constant := (43722109072625777895163427798481629249956055316546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree057.table
  base := (-899543972167544396617323824527228013717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1355614939107417799508844747495322400000000000000)
      constant := (21871745196447704858698886779244367699948465923654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382523709376892261/25000000000000000000)
  centralHi := (74706018967501513809/20000000000000000000)
  directionLo := (47106303455633311461/12500000000000000000)
  directionHi := (376850427645066491689/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree058.table
  base := (-221446479988517859661092737051677866409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-24792673742303296968481649349307063200000000000000)
      constant := (406741741898092064893560873879592211411822417855288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree058.table
  base := (-110746625447974567719517540175983725299/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1377705916507415572305613580077017400000000000000)
      constant := (22607819290139689150785053673337629445668132675752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47106303455633311461/12500000000000000000)
  centralHi := (376850427645066491689/100000000000000000000)
  directionLo := (380141760246387020769/100000000000000000000)
  directionHi := (38014176024638702077/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree059.table
  base := (12217473755636219831922250045370475299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-5038041464497788674616354925458689640000000000000)
      constant := (84040680847909251745067946522503898581011194979558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree059.table
  base := (60917476444019468161607448920930171129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1399796893907413345102382412658712400000000000000)
      constant := (23356060701767330332510869281972741776360385560801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380141760246387020769/100000000000000000000)
  centralHi := (38014176024638702077/10000000000000000000)
  directionLo := (383404839497591224521/100000000000000000000)
  directionHi := (191702419748795612261/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree060.table
  base := (208318996007991648068441946027041775593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-568616464503879772837375553450662960000000000000)
      constant := (9641865161137444516277457196697311180224913910434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree060.table
  base := (1041440728963755828197682007687449088393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1421887871307411117899151245240407400000000000000)
      constant := (24116467409728830833016533461571195078270540818417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383404839497591224521/100000000000000000000)
  centralHi := (191702419748795612261/50000000000000000000)
  directionLo := (386640380737870917361/100000000000000000000)
  directionHi := (193320190368935458681/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree061.table
  base := (205560957535771192002520482273603269727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-5197054896572047236456405036653243640000000000000)
      constant := (89556658695318159369537804721489454101628328539068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree061.table
  base := (2055469551881909418272433762284376876129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1443978848707408890695920077822102400000000000000)
      constant := (24889037612821049494319691080440888690125678705801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386640380737870917361/100000000000000000000)
  centralHi := (193320190368935458681/50000000000000000000)
  directionLo := (77969813924127811967/20000000000000000000)
  directionHi := (97462267405159764959/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree062.table
  base := (1551508836491139355759071966367824425561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-26382808063045882586882150461252603200000000000000)
      constant := (461901458991190201315800075330879048336017780473124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree062.table
  base := (310289058822403967324007193113799719159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-293213965221481332698537782080759480000000000000)
      constant := (5134753941178014181867484446295219340510887955742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77969813924127811967/20000000000000000000)
  centralHi := (97462267405159764959/25000000000000000000)
  directionLo := (393031563810121969081/100000000000000000000)
  directionHi := (196515781905060984541/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree063.table
  base := (4183718120848999736896307500240625511289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-2975593515914614332386919526582109800000000000000)
      constant := (52915378112559696866813441094805755277061127295682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree063.table
  base := (2091801400017120846659471121120688881257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1488160803507404436289457742985492400000000000000)
      constant := (26470662258221364050140890627085628985410040104866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393031563810121969081/100000000000000000000)
  centralHi := (196515781905060984541/50000000000000000000)
  directionLo := (396188494555283714537/100000000000000000000)
  directionHi := (198094247277641857269/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree064.table
  base := (529762074077983630995873127763753460937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-5435575044683435079216480203445074640000000000000)
      constant := (98158820511448733557263824396760113238923301460708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree064.table
  base := (1324379028361741427510693224138063582257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1510251780907402209086226575567187400000000000000)
      constant := (27279713994353770248730702987795113038630018085732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396188494555283714537/100000000000000000000)
  centralHi := (198094247277641857269/50000000000000000000)
  directionLo := (99830117037937933193/25000000000000000000)
  directionHi := (399320468151751732773/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree065.table
  base := (3222322562136802969591716087752671947867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-27575408803602821800682526295211758200000000000000)
      constant := (505568537129046005216758269462821163720650812742828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree065.table
  base := (1611137553820380527993109313321318125769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1532342758307399981882995408148882400000000000000)
      constant := (28100923777039078012672336947158625951354609179844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/25000000000000000000)
  centralHi := (399320468151751732773/100000000000000000000)
  directionLo := (402428067301333079283/100000000000000000000)
  directionHi := (100607016825333269821/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree066.table
  base := (7624719562553688009004233299870755231107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3108104709309829800586961285910904800000000000000)
      constant := (57840187605677017881295888063474173819460218354166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree066.table
  base := (1524926696766549261789153934357404004223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-310886747141479550935952848146115480000000000000)
      constant := (5786858118420367628639256100459704427101074393687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402428067301333079283/100000000000000000000)
  centralHi := (100607016825333269821/25000000000000000000)
  directionLo := (202755926188877622861/50000000000000000000)
  directionHi := (405511852377755245723/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree067.table
  base := (8837780095581277215391296938839652821587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-28370475963974114609882776851184528200000000000000)
      constant := (535773540221055877797096431414365876342639977827654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree067.table
  base := (883770203856990169130435256542368928779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-315304942621479105495306614662454480000000000000)
      constant := (5955962706996587920043056685583098946883719207302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202755926188877622861/50000000000000000000)
  centralHi := (405511852377755245723/100000000000000000000)
  directionLo := (408572362606418178099/100000000000000000000)
  directionHi := (4085723626064181781/1000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree068.table
  base := (80670157332261895130444109450550007207/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-5753601908831952202896580425834182640000000000000)
      constant := (110240815579223476088372183330489162880251052092350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree068.table
  base := (10083698895246223138150591653393487043627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1598615690507393300273301905893967400000000000000)
      constant := (30637491798775817851914130357299956900037068692963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408572362606418178099/100000000000000000000)
  centralHi := (4085723626064181781/1000000000000000000)
  directionLo := (411610117165191355727/100000000000000000000)
  directionHi := (25725632322824459733/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree069.table
  base := (11362637369813255947215598308213040763057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3240615902705045268787003045239699800000000000000)
      constant := (62983698722367200955115708883854978471667552153266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree069.table
  base := (113625732144949881716573891426704855563/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-324141333581478214614014147695132480000000000000)
      constant := (6301464932717289651006138166584626894857853402940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411610117165191355727/100000000000000000000)
  centralHi := (25725632322824459733/6250000000000000000)
  directionLo := (10365640405315493939/2500000000000000000)
  directionHi := (414625616212619757561/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree070.table
  base := (12674337782063128975640741573316413043251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-29563076704531053823683152685143683200000000000000)
      constant := (582721160458974062685155263103818111759992292449542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree070.table
  base := (12674279633371940956058261466816378363879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1642797645307388845866839571057357400000000000000)
      constant := (32389311487067873809351275202948538309600470135551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10365640405315493939/2500000000000000000)
  centralHi := (414625616212619757561/100000000000000000000)
  directionLo := (417619341849305093167/100000000000000000000)
  directionHi := (26101208865581568323/6250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree071.table
  base := (14018830366831269040316006725998704411741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35899020000000000000000000000000000000000000000
      center := (227884365)
      previous := (0)
      next := (202903875)
      square := (5292182168271172138393487672280000000000000000)
      linear := (-421980426545305637018074337508874200000000000000)
      constant := (8433911034324946166009590125392641119715117839382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree071.table
  base := (14018777670522000757829432475999209729489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (12663555)
      previous := (0)
      next := (11269125)
      square := (294010120459509563244082648460000000000000000)
      linear := (-23449135531089952375543780332944400000000000000)
      constant := (468781009802778383418035814529244768889239556671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417619341849305093167/100000000000000000000)
  centralHi := (26101208865581568323/6250000000000000000)
  directionLo := (8411835180353900509/2000000000000000000)
  directionHi := (420591759017695025451/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree072.table
  base := (7698039472331823910117742700630577324803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3373127096100260736987044804568494800000000000000)
      constant := (68345872023785205918111794325314322125947113486828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree072.table
  base := (15396031196721086089551512534715637996969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1686979600107384391460377236220747400000000000000)
      constant := (34189744778778703662286863787691079600979902527761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8411835180353900509/2000000000000000000)
  centralHi := (420591759017695025451/100000000000000000000)
  directionLo := (52942914543129456009/12500000000000000000)
  directionHi := (423543316345035648073/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree073.table
  base := (4201512805325047290895677600411978320419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-30755677445087993037483528519102838200000000000000)
      constant := (631636646558701841765404378193691488831435781738392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree073.table
  base := (16806007963489532564426761473128523168109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1709070577507382164257146068802442400000000000000)
      constant := (35108190278768267087389900701669658734280838850421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52942914543129456009/12500000000000000000)
  centralHi := (423543316345035648073/100000000000000000000)
  directionLo := (85294889386762918193/20000000000000000000)
  directionHi := (213237223466907295483/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree074.table
  base := (285136224492310324723054876015332400261/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-31153211025273639442083653797089223200000000000000)
      constant := (648379071122893529497404982951009322367459857533568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree074.table
  base := (18248679183307619786381886612893422214177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1731161554907379937053914901384137400000000000000)
      constant := (36038787788329811166348508812800296037541100515913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85294889386762918193/20000000000000000000)
  centralHi := (213237223466907295483/50000000000000000000)
  directionLo := (429385569103638057947/100000000000000000000)
  directionHi := (107346392275909514487/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree075.table
  base := (19724054644813955428318450680711744688477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3505638289495476205187086563897289800000000000000)
      constant := (73926679482926855155740381902692216221397373345226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree075.table
  base := (3944803831139958540438308210676306862403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-350650506461475541970136746793166480000000000000)
      constant := (7396307388708051731848042642777292296967486226107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429385569103638057947/100000000000000000000)
  centralHi := (107346392275909514487/25000000000000000000)
  directionLo := (43227708708813983399/10000000000000000000)
  directionHi := (432277087088139833991/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree076.table
  base := (5308009268013433539681130708093316615161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-31948278185644932251283904353061993200000000000000)
      constant := (682519773371537165113255348716100097434965515999048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree076.table
  base := (21232004934104173675902067825908215618523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1775343509707375482647452566547527400000000000000)
      constant := (37936437419472415409782589646083552811646725210387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/10000000000000000000)
  centralHi := (432277087088139833991/100000000000000000000)
  directionLo := (217574695845104725947/50000000000000000000)
  directionHi := (87029878338041890379/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree077.table
  base := (22772645128221122603541563131702682585589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-32345811765830578655884029631048378200000000000000)
      constant := (699918039968023482496289076417972152308225349681738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree077.table
  base := (2846577003627289542870245159862754897041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1797434487107373255444221399129222400000000000000)
      constant := (38903488925991464051540153180160863496681425279432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217574695845104725947/50000000000000000000)
  centralHi := (87029878338041890379/20000000000000000000)
  directionLo := (219001430449273220717/50000000000000000000)
  directionHi := (87600572179709288287/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree078.table
  base := (24345860487619102532270766044972889880671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3638149482890691673387128323226084800000000000000)
      constant := (79726101162765693974871736388671479217257382386798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree078.table
  base := (12172917071709973823766686938498942616693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1819525464507371028240990231710917400000000000000)
      constant := (39882691204008477001278093458421389967547350202234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219001430449273220717/50000000000000000000)
  centralHi := (87600572179709288287/20000000000000000000)
  directionLo := (110209465117073633199/25000000000000000000)
  directionHi := (440837860468294532797/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree079.table
  base := (12975833391877893006301672354341543896729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-33140878926201871465084280187021148200000000000000)
      constant := (735370380690599215681415048277214856561999642739236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree079.table
  base := (5190328587382128246715002621515086719011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-368323288381473760207551812858522480000000000000)
      constant := (8174808804428130202892162321581598771490851272859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110209465117073633199/25000000000000000000)
  centralHi := (440837860468294532797/100000000000000000000)
  directionLo := (22182737223414044671/5000000000000000000)
  directionHi := (443654744468280893421/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree080.table
  base := (5518009879765974148103842320663567073441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-6707682501277503573936881093001506640000000000000)
      constant := (150684889383863545787237418003881290634249679487522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree080.table
  base := (27590027815427936366124259989876458928587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1863707419307366573834527896874307400000000000000)
      constant := (41877547173733595250525372735170530947550350851203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22182737223414044671/5000000000000000000)
  centralHi := (443654744468280893421/100000000000000000000)
  directionLo := (446453855797178340827/100000000000000000000)
  directionHi := (111613463949294585207/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree081.table
  base := (7315248819000341279205138231749379299861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3770660676285907141587170082554879800000000000000)
      constant := (85744122869231076619122641020338382343499067492072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree081.table
  base := (29260975743723474239201018296408072859607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1885798396707364346631296729456002400000000000000)
      constant := (42893200474205989991806460466991439492156348393583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446453855797178340827/100000000000000000000)
  centralHi := (111613463949294585207/25000000000000000000)
  directionLo := (449235526670720699369/100000000000000000000)
  directionHi := (44923552667072069937/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree082.table
  base := (30964492751955502992733654536578657095293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-34333479666758810678884656020980303200000000000000)
      constant := (790188354429103950189647016937688987667723163721306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree082.table
  base := (7741118769529157606685833198240414033109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1907889374107362119428065562037697400000000000000)
      constant := (43921003758681349814405509512783890861355180141684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449235526670720699369/100000000000000000000)
  centralHi := (44923552667072069937/10000000000000000000)
  directionLo := (226000039540965515079/50000000000000000000)
  directionHi := (452000079081931030159/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree083.table
  base := (32700531407544349250596427507042451338299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-34731013246944457083484781298966688200000000000000)
      constant := (808898190081726390038008492130053790301492620225558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree083.table
  base := (32700515417309586722664175485294271782383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1929980351507359892224834394619392400000000000000)
      constant := (44960956879875539793193050727441674040670474502727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226000039540965515079/50000000000000000000)
  centralHi := (452000079081931030159/100000000000000000000)
  directionLo := (113686956309041892219/25000000000000000000)
  directionHi := (454747825236167568877/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree084.table
  base := (17234550967267932970089805450514840211187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-3903171869681122609787211841883674800000000000000)
      constant := (91980734489826279071397146237223773297593614442412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree084.table
  base := (17234543734647472438630843414094182384297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1952071328907357665021603227201087400000000000000)
      constant := (46013059706212164819703001580190245308956936932386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113686956309041892219/25000000000000000000)
  centralHi := (454747825236167568877/100000000000000000000)
  directionLo := (228739533981325634129/50000000000000000000)
  directionHi := (457479067962651268259/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree085.table
  base := (36270196016717802848289834688018692548193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-35526080407315749892685031854939458200000000000000)
      constant := (846973613289572838751340614264958504340796163443106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree085.table
  base := (18135091466302238392708217673746218023183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1974162306307355437818372059782782400000000000000)
      constant := (47077312120141031835836321156171700308138234395854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228739533981325634129/50000000000000000000)
  centralHi := (457479067962651268259/100000000000000000000)
  directionLo := (230097050552005226279/50000000000000000000)
  directionHi := (460194101104010452559/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree086.table
  base := (9525951555949224463935307903035250644363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-35923613987501396297285157132925843200000000000000)
      constant := (866339196831279621763265926110303472444870806368984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree086.table
  base := (19051897195170315964612779480335599326787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-1996253283707353210615140892364477400000000000000)
      constant := (48153714016637618070573467402713647426367180294006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230097050552005226279/50000000000000000000)
  centralHi := (460194101104010452559/100000000000000000000)
  directionLo := (18515728395410439951/4000000000000000000)
  directionHi := (57861651235657624847/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree087.table
  base := (4996240739588167594894971798792407238209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-4035683063076338077987253601212469800000000000000)
      constant := (98435928815707895685492848992594690099807803157136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree087.table
  base := (39969915215603802528304080580230057846639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2018344261107350983411909724946172400000000000000)
      constant := (49242265301863905131710474159196035415488184321991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18515728395410439951/4000000000000000000)
  centralHi := (57861651235657624847/12500000000000000000)
  directionLo := (232788335631766775193/50000000000000000000)
  directionHi := (465576671263533550387/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree088.table
  base := (8373709832615750814929056889634078524409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-7343736229574537821297081537779722640000000000000)
      constant := (181145219861557615636863395038941489521168237172178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree088.table
  base := (10467134871770141060198822532060060258403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2040435238507348756208678557527867400000000000000)
      constant := (50342965891973094228597936637131389685636680600428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232788335631766775193/50000000000000000000)
  centralHi := (465576671263533550387/100000000000000000000)
  directionLo := (468244754259761551517/100000000000000000000)
  directionHi := (234122377129880775759/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree089.table
  base := (43799670661805266735888060494343403346443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-37116214728058335511085532966884998200000000000000)
      constant := (925747415379367153128217128515133603518824371719606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree089.table
  base := (43799661913693356090006836633491498231883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2062526215907346529005447390109562400000000000000)
      constant := (51455815712042632905698086085760058962526664468227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468244754259761551517/100000000000000000000)
  centralHi := (234122377129880775759/50000000000000000000)
  directionLo := (5886221503418180969/1250000000000000000)
  directionHi := (470897720273454477521/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree090.table
  base := (9152657135133106981527854579097750826707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-833638851294310709237459072108252960000000000000)
      constant := (21021940141081586867181420719349726813452121666966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree090.table
  base := (45763277767332270586676171592818003921279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2084617193307344301802216222691257400000000000000)
      constant := (52580814695121685822388599132906518121767973336151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5886221503418180969/1250000000000000000)
  centralHi := (470897720273454477521/100000000000000000000)
  directionLo := (94707164676319748107/20000000000000000000)
  directionHi := (59191977922699842567/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree091.table
  base := (23879694985595252699377260245273395501343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-37911281888429628320285783522857768200000000000000)
      constant := (966445771136661375378938694332320540315352837850812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree091.table
  base := (9551876564559300097435155468827191886569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-421341634141468414919797011054590480000000000000)
      constant := (10743592556276139097832657191085035136409245870161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94707164676319748107/20000000000000000000)
  centralHi := (59191977922699842567/12500000000000000000)
  directionLo := (119039827655663414539/25000000000000000000)
  directionHi := (476159310622653658157/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree092.table
  base := (9957595952991765900700310205113510228557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-7661763093723054944977181760168830640000000000000)
      constant := (197424561755801421933936323021576796322352723430394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree092.table
  base := (1555874165755251252423393501243483492769/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2128799148107339847395753887854647400000000000000)
      constant := (54867259917352024814969548898809800265002218174752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119039827655663414539/25000000000000000000)
  centralHi := (476159310622653658157/100000000000000000000)
  directionLo := (239384211133270477681/50000000000000000000)
  directionHi := (478768422266540955363/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree093.table
  base := (5184905167564045168677635900774324351699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-860141089973353802877467423974011960000000000000)
      constant := (22400409298085887140768365510911921590973493108524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree093.table
  base := (25924522918462399575856207249159664285923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2150890125507337620192522720436342400000000000000)
      constant := (56028706055251870708256019166438844796043868001974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384211133270477681/50000000000000000000)
  centralHi := (478768422266540955363/100000000000000000000)
  directionLo := (96272678414292591171/20000000000000000000)
  directionHi := (30085212004466434741/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree094.table
  base := (5394260268116819751094302944491207799273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-7820776525797313506817231871363384640000000000000)
      constant := (205826519854192227164922782336024481407265655256932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree094.table
  base := (13485649351293883953066183154764027189779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2172981102907335392989291553018037400000000000000)
      constant := (57202301152374703498135596525942370220511462850604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96272678414292591171/20000000000000000000)
  centralHi := (30085212004466434741/6250000000000000000)
  directionLo := (483944447528326397757/100000000000000000000)
  directionHi := (241972223764163198879/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree095.table
  base := (56068630080486212074097824686532778647571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-39501416209172213938686284634803308200000000000000)
      constant := (1050465350661842420230486169931601894585655542390982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree095.table
  base := (56068625313465993072005012181908112249939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2195072080307333165786060385599732400000000000000)
      constant := (58388045170552435373900090575873566549430106479691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483944447528326397757/100000000000000000000)
  centralHi := (241972223764163198879/50000000000000000000)
  directionLo := (121627952523373805271/25000000000000000000)
  directionHi := (97302362018699044217/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree096.table
  base := (11645426291876755582362545021553019472803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-886643328652396896517475775839770960000000000000)
      constant := (23822592710470386730130161829187998956390362767414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree096.table
  base := (58227127152665257620338854520271248857747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2217163057707330938582829218181427400000000000000)
      constant := (59585938075671365459947135140659945209666754479243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121627952523373805271/25000000000000000000)
  centralHi := (97302362018699044217/20000000000000000000)
  directionLo := (489065695410546306787/100000000000000000000)
  directionHi := (122266423852636576697/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree097.table
  base := (30209052329988094129525819918343254475453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-40296483369543506747886535190776078200000000000000)
      constant := (1093786562648927865355176870744472536783017149936052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree097.table
  base := (944032824523351019279117371474015020201/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2239254035107328711379598050763122400000000000000)
      constant := (60795979837240701134745293555542228722353412734016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489065695410546306787/100000000000000000000)
  centralHi := (122266423852636576697/25000000000000000000)
  directionLo := (245803156760828313457/50000000000000000000)
  directionHi := (98321262704331325383/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree098.table
  base := (15660386938360423285876955796000426399301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-40694016949729153152486660468762463200000000000000)
      constant := (1115775022203499852619739976126231670930803782214568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree098.table
  base := (15660386059826820319174447783082717612651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2261345012507326484176366883344817400000000000000)
      constant := (62018170428007125034619934666384106689497658792076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245803156760828313457/50000000000000000000)
  centralHi := (98321262704331325383/20000000000000000000)
  directionLo := (123533467267302064021/25000000000000000000)
  directionHi := (98826773813841651217/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree099.table
  base := (64897459015665715147679293017925583642451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-4565727836657199950787420638527649800000000000000)
      constant := (126442450021715088488981021023550924818851483468438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree099.table
  base := (64897455841773729483514810930255821581121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2283435989907324256973135715926512400000000000000)
      constant := (63252509823610473959888040988580378184322520569449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123533467267302064021/25000000000000000000)
  centralHi := (98826773813841651217/20000000000000000000)
  directionLo := (496648561488158892363/100000000000000000000)
  directionHi := (124162140372039723091/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree100.table
  base := (6718583690548111935448371288344807171591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-8297816822020089192337382204947046640000000000000)
      constant := (232081529246383665824070829264306406193597060119644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree100.table
  base := (67185834039156498048737010703729541597427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2305526967307322029769904548508207400000000000000)
      constant := (64498998002276127697776939123347671739312096285163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496648561488158892363/100000000000000000000)
  centralHi := (124162140372039723091/25000000000000000000)
  directionLo := (99830117037937933193/20000000000000000000)
  directionHi := (249575292594844832983/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree101.table
  base := (69506680045226824273102301578767013355701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-41886617690286092366287036302721618200000000000000)
      constant := (1183051809961805003482925061431505044204605698922442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree101.table
  base := (69506677456902325047330203753314110356793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2327617944707319802566673381089902400000000000000)
      constant := (65757634944540179759926879656244394200236839178017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/20000000000000000000)
  centralHi := (249575292594844832983/50000000000000000000)
  directionLo := (250820064868304414183/50000000000000000000)
  directionHi := (501640129736608828367/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree102.table
  base := (8982498400422113362857148506449698151113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-4698239030052415418987462397856444800000000000000)
      constant := (133990504563466749548030154522887474028099961889552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree102.table
  base := (17964996216575226167294591362078302141909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2349708922107317575363442213671597400000000000000)
      constant := (67028420633003884564024937768891723098249973690484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250820064868304414183/50000000000000000000)
  centralHi := (501640129736608828367/100000000000000000000)
  directionLo := (504117380010959187041/100000000000000000000)
  directionHi := (252058690005479593521/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree103.table
  base := (74245757279018984717462542902153753407073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-42681684850657385175487286858694388200000000000000)
      constant := (1228995839279501659434625756986068198651362630556066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree103.table
  base := (37122877584495180332495509113580464626679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2371799899507315348160211046253292400000000000000)
      constant := (68311355052114252319224074168927177285924593097502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504117380010959187041/100000000000000000000)
  centralHi := (252058690005479593521/50000000000000000000)
  directionLo := (253291258187124338881/50000000000000000000)
  directionHi := (506582516374248677763/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree104.table
  base := (76663989287984404888514969534404853280699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-43079218430843031580087412136680773200000000000000)
      constant := (1252295704335859843916042798544219100463748241006358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree104.table
  base := (76663987383112058258189899031799231629357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2393890876907313120956979878834987400000000000000)
      constant := (69606438187967998822978663409722198093941840481333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253291258187124338881/50000000000000000000)
  centralHi := (506582516374248677763/100000000000000000000)
  directionLo := (254517857410348530797/50000000000000000000)
  directionHi := (101807142964139412319/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree105.table
  base := (79114682350453951705750521375715187470309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-4830750223447630887187504157185239800000000000000)
      constant := (141757126224002700140692916672786790132142515844442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree105.table
  base := (39557340315469342804117366662861313783791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2415981854307310893753748711416682400000000000000)
      constant := (70913670028136357003710954152533471140981020041358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254517857410348530797/50000000000000000000)
  centralHi := (101807142964139412319/20000000000000000000)
  directionLo := (511477147123867228731/100000000000000000000)
  directionHi := (127869286780966807183/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree106.table
  base := (20399458919970419276544422594963794260347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (305279055)
      previous := (0)
      next := (271814625)
      square := (7089527055608551355206370277960000000000000000)
      linear := (-827816709268194799797880428163274400000000000000)
      constant := (24519832719236185048493147704295542624882217610232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree106.table
  base := (40798917063909205392378956791547893859537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16964385)
      previous := (0)
      next := (15096375)
      square := (393862614200475075289242793220000000000000000)
      linear := (-46001374183156767293405991396195800000000000000)
      constant := (1362887746443557062549572544201311250892268157802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511477147123867228731/100000000000000000000)
  centralHi := (127869286780966807183/25000000000000000000)
  directionLo := (513906980977026832737/100000000000000000000)
  directionHi := (256953490488513416369/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree107.table
  base := (10514181071637039461399128817666364616873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-44271819171399970793887787970639928200000000000000)
      constant := (1323506698467113931655959144492404009018288038141328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree107.table
  base := (84113447172294759189954338820854662299011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2460163809107306439347286376580072400000000000000)
      constant := (73564579778151758530778708221148020480091924292859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513906980977026832737/100000000000000000000)
  centralHi := (256953490488513416369/50000000000000000000)
  directionLo := (516325380127564826781/100000000000000000000)
  directionHi := (258162690063782413391/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree108.table
  base := (17332304080290957253714802966925461811669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-992652283368569271077509183302806960000000000000)
      constant := (29948462864412938059048367424891363579312558424122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree108.table
  base := (5416344946079805062604895162536735157183/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2482254786507304212144055209161767400000000000000)
      constant := (74908257669186347238829841425380128916543245502832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516325380127564826781/100000000000000000000)
  centralHi := (258162690063782413391/50000000000000000000)
  directionLo := (129683126126441950197/25000000000000000000)
  directionHi := (518732504505767800789/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree109.table
  base := (89242050602935704059509050026628907850287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-45066886331771263603088038526612698200000000000000)
      constant := (1372073525270672930352313001182662735369268831133054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree109.table
  base := (89242049462148285639764531334867079148147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2504345763907301984940824041743462400000000000000)
      constant := (76264084226673866188478695283826464720774137556843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129683126126441950197/25000000000000000000)
  centralHi := (518732504505767800789/100000000000000000000)
  directionLo := (104225702069648541783/20000000000000000000)
  directionHi := (130282127587060677229/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree110.table
  base := (22963759668768201707140128462302842389279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-45464419911956910007688163804599083200000000000000)
      constant := (1396684787455315955320430484315111659548703918826872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree110.table
  base := (45927518822857042972081778914692733994691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2526436741307299757737592874325157400000000000000)
      constant := (77632059443517311075603040142265822892873739325558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104225702069648541783/20000000000000000000)
  centralHi := (130282127587060677229/25000000000000000000)
  directionLo := (52351355031625552429/10000000000000000000)
  directionHi := (523513550316255524291/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree111.table
  base := (18900096833727778126768415365375591073209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-1019154522047612364717517535168565960000000000000)
      constant := (31589213674178019806037035658722872452393061624642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree111.table
  base := (94500483239897474902685611291619309120217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2548527718707297530534361706906852400000000000000)
      constant := (79012183313371838587929883503001425038305514036673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52351355031625552429/10000000000000000000)
  centralHi := (523513550316255524291/100000000000000000000)
  directionLo := (262943886804619732807/50000000000000000000)
  directionHi := (105177554721847893123/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree112.table
  base := (48589193341000197923982911173216015414643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-46259487072328202816888414360571853200000000000000)
      constant := (1446563008816388154758904343464501642264006198368012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree112.table
  base := (97178385844105691478137418654626695970937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2570618696107295303331130539488547400000000000000)
      constant := (80404455830564987528995953333742225446860087008353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262943886804619732807/50000000000000000000)
  centralHi := (105177554721847893123/20000000000000000000)
  directionLo := (528251326073711619383/100000000000000000000)
  directionHi := (66031415759213952423/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree113.table
  base := (99888745856071305547218031747767712893267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-46657020652513849221488539638558238200000000000000)
      constant := (1471829967798922809448964066231808853752868514278214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree113.table
  base := (2497218627504856081339243107749752560437/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-518541934701458615225579874414048480000000000000)
      constant := (16361775398005074271951605942129766825211765070824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528251326073711619383/100000000000000000000)
  centralHi := (66031415759213952423/12500000000000000000)
  directionLo := (106120870061564590203/20000000000000000000)
  directionHi := (66325543788477868877/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree114.table
  base := (51315780684901313380403899564894170025339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-5228283803633277291787629435171624800000000000000)
      constant := (166368388022642767931379329966938180733694138089164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree114.table
  base := (12828945085995719076877127819048597152423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2614800650907290848924668204651937400000000000000)
      constant := (83225446787218941099845544312763445039129827515896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106120870061564590203/20000000000000000000)
  centralHi := (66325543788477868877/12500000000000000000)
  directionLo := (532946985761753783631/100000000000000000000)
  directionHi := (33309186610109611477/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree115.table
  base := (105406832936150518837792346874091494143277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-47452087812885142030688790194531008200000000000000)
      constant := (1523019581957811853266778498549098037294813625608634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree115.table
  base := (105406832321146578374422639388209059206877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2636891628307288621721437037233632400000000000000)
      constant := (84654165218092013609790253854758583823200384282213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532946985761753783631/100000000000000000000)
  centralHi := (33309186610109611477/6250000000000000000)
  directionLo := (53527936883415475663/10000000000000000000)
  directionHi := (535279368834154756631/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree116.table
  base := (54107280149236100023854364338728355468667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-47849621393070788435288915472517393200000000000000)
      constant := (1548942236995589742187255232949724599507022361290028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree116.table
  base := (108214559743790423755380262366998269033637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2658982605707286394518205869815327400000000000000)
      constant := (86095032279020346072314089739669036412223766604653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53527936883415475663/10000000000000000000)
  centralHi := (535279368834154756631/100000000000000000000)
  directionLo := (537601632964821994863/100000000000000000000)
  directionHi := (33600102060301374679/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree117.table
  base := (444218972909216726715941137883999930343/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359550887)
      previous := (0)
      next := (320137225)
      square := (8349887421050071596131947216264000000000000000)
      linear := (-1072158999405698551997534238900083960000000000000)
      constant := (35001854605747382802513469501888360617214510796700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree117.table
  base := (27763685681765888163948646799179983908183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2681073583107284167314974702397022400000000000000)
      constant := (87548047966763614111309981204613141021728607051708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537601632964821994863/100000000000000000000)
  centralHi := (33600102060301374679/6250000000000000000)
  directionLo := (539913908723784665747/100000000000000000000)
  directionHi := (134978477180946166437/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree118.table
  base := (28481845379370554513947893709058513139279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-48644688553442081244489166028490163200000000000000)
      constant := (1601443242694646417996840174179672179114745604826872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree118.table
  base := (11392738106637106872634123667948756611131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-540632912101456388022348706995743480000000000000)
      constant := (17802642455684943883586802406529815693906964482278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539913908723784665747/100000000000000000000)
  centralHi := (134978477180946166437/25000000000000000000)
  directionLo := (271108161948486611677/50000000000000000000)
  directionHi := (108443264779394644671/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree119.table
  base := (116832474985566683229488437216322058902843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-49042222133627727649089291306476548200000000000000)
      constant := (1628021593256876667953326087220993376256109806288406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree119.table
  base := (116832474578788028179454344288423915081573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2725255537907279712908512367560412400000000000000)
      constant := (90490525211413413873838749455124823918696722465837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271108161948486611677/50000000000000000000)
  centralHi := (108443264779394644671/20000000000000000000)
  directionLo := (544509003568627386753/100000000000000000000)
  directionHi := (272254501784313693377/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree120.table
  base := (59885011733770473031535112373059083135417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-5493306190423708228187712953829214800000000000000)
      constant := (183868723211501990899974660962752631656730218421892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree120.table
  base := (23954004620152602553979429423913813602209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-549469303061455497141056240028421480000000000000)
      constant := (18395997352682756351296391492861474842041778213321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544509003568627386753/100000000000000000000)
  centralHi := (272254501784313693377/50000000000000000000)
  directionLo := (273396035100297115029/50000000000000000000)
  directionHi := (546792070200594230059/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree121.table
  base := (981920214534030115803570477208232789189/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3235957983)
      previous := (0)
      next := (2881235025)
      square := (75148986789450644365187524946376000000000000000)
      linear := (-9967457858799804091657908372489863640000000000000)
      constant := (336366797919438250748294193725227016115065925823450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree121.table
  base := (30685006621516308369942479523651608544501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2769437492707275258502050032723802400000000000000)
      constant := (93481596932355170380366831899713890183947912722676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273396035100297115029/50000000000000000000)
  centralHi := (546792070200594230059/100000000000000000000)
  directionLo := (274532821854329316281/50000000000000000000)
  directionHi := (549065643708658632563/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree122.table
  base := (125742484902079800871190462611911547797523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-50234822874184666862889667140435703200000000000000)
      constant := (1709068035304475049948823944489624728012561062304966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree122.table
  base := (31435621150987328045321465924561902886141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2791528470107273031298818865305497400000000000000)
      constant := (94995355716386203095235008169199783983317377271316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274532821854329316281/50000000000000000000)
  centralHi := (549065643708658632563/100000000000000000000)
  directionLo := (551329841536040711181/100000000000000000000)
  directionHi := (275664920768020355591/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree123.table
  base := (128777397606275113619968683364557837008127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-5625817383818923696387754713158009800000000000000)
      constant := (192946738443942868247002322976874730095869065386926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree123.table
  base := (3219434933437865931792789417761967687591/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4174943710525035798065973608132000000000000000)
      linear := (-562723889501454160819117539577438480000000000000)
      constant := (19304252622770309496917684072916767741330622103032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551329841536040711181/100000000000000000000)
  centralHi := (275664920768020355591/50000000000000000000)
  directionLo := (276792389362093849561/50000000000000000000)
  directionHi := (553584778724187699123/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree124.table
  base := (2060074450382920921872219492898166764061/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-51029890034555959672089917696408473200000000000000)
      constant := (1764191821643503452845341722692065563827018493027968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree124.table
  base := (131844764582238645073627326436046996708527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2835710424907268576892356530468887400000000000000)
      constant := (98059319123271146382441543615286788265335186061063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276792389362093849561/50000000000000000000)
  centralHi := (553584778724187699123/100000000000000000000)
  directionLo := (555830567980981012029/100000000000000000000)
  directionHi := (55583056798098101203/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree125.table
  base := (33736146615759818908354296190456618966757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-51427423614741606076690042974394858200000000000000)
      constant := (1792081562224636248639815472896358922176377684139176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree125.table
  base := (33736146561166393248015905937569534881403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2857801402307266349689125363050582400000000000000)
      constant := (99609523743321650396425731405459581940188245748428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555830567980981012029/100000000000000000000)
  centralHi := (55583056798098101203/10000000000000000000)
  directionLo := (279033659873236463017/50000000000000000000)
  directionHi := (111613463949294585207/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree126.table
  base := (69038431219028873555639258969901819814853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-5758328577214139164587796472486804800000000000000)
      constant := (202243318635280148709317998299497856902943468760628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree126.table
  base := (138076862241234190974096935238048966492487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2879892379707264122485894195632277400000000000000)
      constant := (101171876972819818387143707557866928495808953150303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279033659873236463017/50000000000000000000)
  centralHi := (111613463949294585207/20000000000000000000)
  directionLo := (560295142256261353567/100000000000000000000)
  directionHi := (17509223195508167299/3125000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree127.table
  base := (141241592674618973191841099912974359414003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-52222490775112898885890293530367628200000000000000)
      constant := (1848516738103056925343748489515079475926692422037126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree127.table
  base := (35310398124307442420125728885990973649777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2901983357107261895282663028213972400000000000000)
      constant := (102746378810707677160362797013362061414921556529252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560295142256261353567/100000000000000000000)
  centralHi := (17509223195508167299/3125000000000000000)
  directionLo := (112502828320521123411/20000000000000000000)
  directionHi := (17578566925081425533/3125000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree128.table
  base := (144438777105711247996519530824183005999577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16179789915)
      previous := (0)
      next := (14406175125)
      square := (375744933947253221825937624731880000000000000000)
      linear := (-52620024355298545290490418808354013200000000000000)
      constant := (1877062173364162862075531857982777021333876436473234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree128.table
  base := (36109694236461777307578246610610477950807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2924074334507259668079431860795667400000000000000)
      constant := (104333029256039253795689704820581033443816803225532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell138.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502828320521123411/20000000000000000000)
  centralHi := (17578566925081425533/3125000000000000000)
  directionLo := (17647638181043152003/3125000000000000000)
  directionHi := (564724421793380864097/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree129.table
  base := (147668415671414724890384282330671694449681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1797754435)
      previous := (0)
      next := (1600686125)
      square := (41749437105250357980659736081320000000000000000)
      linear := (-5890839770609354632787838231815599800000000000000)
      constant := (211758463720618510643636420939882888885097689912178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree129.table
  base := (73834207763676425653396102718447148006521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20874718552625178990329868040660000000000000000)
      linear := (-2946165311907257440876200693377362400000000000000)
      constant := (105931828307968713844421908665566866354180700924098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell138.Kernel129
