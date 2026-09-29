import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell118.Parameters
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch000_049
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch050_099
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch100_149
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree000.table
  base := (998275122717089459034411903/20000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18299405747519981169091352000000000000)
      linear := (-1048632918412890739634502060000000000)
      constant := (9982751227170894590344119030000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree000.table
  base := (998275122717089459034411903/20000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18299405747519981169091352000000000000)
      linear := (-1048632918412890739634502060000000000)
      constant := (9982751227170894590344119030000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree001.table
  base := (139438314466931790992322958322929277024407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-1103858486191703424990416360468643500000000000)
      constant := (304493138535305626205987677030656512527777578303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree001.table
  base := (278640710832752772749848359971913620625207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-19889723918167476908967555433613583000000000000)
      constant := (5476255750220153381384084201771596457999984813527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12484442801072604411/25000000000000000000)
  directionHi := (9987554240858083529/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree002.table
  base := (163656081241950414697078655515633496891527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-4301052788673195943844459659652087000000000000)
      constant := (359335824825218508519316240598947945840276004783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree002.table
  base := (16341033435651127200544102437023688547561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-3875001743149239401288025882722478300000000000)
      constant := (322924119097838698797727589211587715881249806921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/25000000000000000000)
  centralHi := (9987554240858083529/20000000000000000000)
  directionLo := (70622673311792116403/100000000000000000000)
  directionHi := (17655668327948029101/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree003.table
  base := (101876858043053478823003600616371738241337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-6394388604962985037708086598366887000000000000)
      constant := (227366862071001100684328840280413800253885664273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree003.table
  base := (50840318117982857655830430269828960370813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-3200572830267628395377386790046443500000000000)
      constant := (113474813749068593894100670081841855088779313077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70622673311792116403/100000000000000000000)
  centralHi := (17655668327948029101/25000000000000000000)
  directionLo := (8649475694258104387/10000000000000000000)
  directionHi := (86494756942581043871/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree004.table
  base := (67522537306670541005526154383055565504371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-8487724421252774131571713537081687000000000000)
      constant := (156323809672179522274180238574295062759184963259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree004.table
  base := (33689370447180863493594783032286441934929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-38235302229071114110352832807223591500000000000)
      constant := (702131756038981959951238497644868320490773537969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8649475694258104387/10000000000000000000)
  centralHi := (86494756942581043871/100000000000000000000)
  directionLo := (12484442801072604411/12500000000000000000)
  directionHi := (99875542408580835289/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree005.table
  base := (47437839237670702098090686825947856729167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-10581060237542563225435340475796487000000000000)
      constant := (117508043252561658004584078544710499442522956343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree005.table
  base := (23667301208308583284472517972107125926023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-47665448985733572662309184504029191500000000000)
      constant := (527907125453412818091343660301826271828439262503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12484442801072604411/12500000000000000000)
  centralHi := (99875542408580835289/100000000000000000000)
  directionLo := (27916062764406227853/25000000000000000000)
  directionHi := (111664251057624911413/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree006.table
  base := (17467890010959825980787840380261493226873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-6337198026916176159649483707255643500000000000)
      constant := (48165856849541450206026367964809553557727028817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree006.table
  base := (34860566308875606544263025104363898724603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-12687910164976895825392341377963287000000000000)
      constant := (96210561554096308092996530709141683620784457987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/25000000000000000000)
  centralHi := (111664251057624911413/100000000000000000000)
  directionLo := (3822564323198829159/3125000000000000000)
  directionHi := (122322058342362533089/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree007.table
  base := (13296294924327426885797778596922685667609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-150691141531858585848597901563531500000000000)
      constant := (870671100818778196945113907899399138607620289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree007.table
  base := (3316982562629636885563042857643028783899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-1357668214266499791147385467298783500000000000)
      constant := (7830033674063975811737821811274747241566825644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822564323198829159/3125000000000000000)
  centralHi := (122322058342362533089/100000000000000000000)
  directionLo := (132122923635394931437/100000000000000000000)
  directionHi := (66061461817697465719/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree008.table
  base := (10316629025502921827913460089361462702873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-8430533843205965253513110645970443500000000000)
      constant := (40308984275473245244681787020497260368735832817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree008.table
  base := (10294309150995358164026006398910772580419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-75955889255720948318178239594445991500000000000)
      constant := (362685290991950829902301907731408441169299925859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132122923635394931437/100000000000000000000)
  centralHi := (66061461817697465719/50000000000000000000)
  directionLo := (141245346623584232807/100000000000000000000)
  directionHi := (17655668327948029101/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree009.table
  base := (4029974131762326719669267204579891847537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-9477201751350859800444924115327843500000000000)
      constant := (40081142809050457553228579967702701514531088146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree009.table
  base := (2010416095586492159850345309833466978529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-9487337334709267430014954587916843500000000000)
      constant := (40089405634255935910986390440832032536813563364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141245346623584232807/100000000000000000000)
  centralHi := (17655668327948029101/12500000000000000000)
  directionLo := (149813313612871252933/100000000000000000000)
  directionHi := (74906656806435626467/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree010.table
  base := (3135694274148324260322062982708045634733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-10523869659495754347376737584685243500000000000)
      constant := (41423366137248790258174084789742997670986893514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree010.table
  base := (3127960477231647069592297503498439793237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-94816182769045865422090942988057191500000000000)
      constant := (373041281546352726721765140404150651546609348714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/100000000000000000000)
  centralHi := (74906656806435626467/50000000000000000000)
  directionLo := (78958549138963686213/50000000000000000000)
  directionHi := (157917098277927372427/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree011.table
  base := (480684496355068052250733847353458026777/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-2314107513528129778861710210808528700000000000)
      constant := (8804257041237307072720094575556029321393604066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree011.table
  base := (2396730709612311691964407286868571652631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-104246329525708323974047294684862791500000000000)
      constant := (396575432854227528538301453196167397478264150382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/50000000000000000000)
  centralHi := (157917098277927372427/100000000000000000000)
  directionLo := (16562484995124562987/10000000000000000000)
  directionHi := (165624849951245629871/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree012.table
  base := (7161089017487068781837970941282364562427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-25234410951571086882480729046800087000000000000)
      constant := (95375567455523306951900275393293889481506810883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree012.table
  base := (3568800124536056170209757857067117522749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-12630719586930086947333738486852043500000000000)
      constant := (47747633307754115832955857371043983822285103221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/10000000000000000000)
  centralHi := (165624849951245629871/100000000000000000000)
  directionLo := (172989513885162087741/100000000000000000000)
  directionHi := (86494756942581043871/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree013.table
  base := (5076523221214120477573408815445524999743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-27327746767860875976344355985514887000000000000)
      constant := (104609134082696101680368729334314634207164347047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree013.table
  base := (2527875417916713153972684881625993402519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-123106623039033241077959998078473991500000000000)
      constant := (471439648728956626485661394240456012852634843959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172989513885162087741/100000000000000000000)
  centralHi := (86494756942581043871/50000000000000000000)
  directionLo := (180053194659458191969/100000000000000000000)
  directionHi := (18005319465945819197/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree014.table
  base := (1643485754851595675092134144501686777147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-300215128409700663981714111471731500000000000)
      constant := (1179428293902406419389535906720868097005361587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree014.table
  base := (40856706838903798404663611207315350003/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400689000000000000000000000000000000000000000
      center := (4006890)
      previous := (2003445)
      next := (2003445)
      square := (36661852947840168673310223707640000000000000)
      linear := (-540966407329370202571087141939916700000000000)
      constant := (2126503009318862135259735494191998642218816536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/100000000000000000000)
  centralHi := (18005319465945819197/10000000000000000000)
  directionLo := (186850030505560263907/100000000000000000000)
  directionHi := (46712507626390065977/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree015.table
  base := (1740314949136156523185784471243979086883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-31514418400440454164071609862944487000000000000)
      constant := (128186384649169169067644711299015298953428784107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree015.table
  base := (344787935529635466736549703321817711501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-6309640735660362585861008954314897400000000000)
      constant := (25683502837149049688100829975832647670353065029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/100000000000000000000)
  centralHi := (46712507626390065977/25000000000000000000)
  directionLo := (2417601952761663603/1250000000000000000)
  directionHi := (193408156220933088241/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree016.table
  base := (397513617787448249123356678847286138749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-33607754216730243257935236801659287000000000000)
      constant := (142331202901494065500242419081342793282978967221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree016.table
  base := (382976983459696343791521677857813169521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-302794126618041233467658106337781583000000000000)
      constant := (1283427369078973100841598626304446783753027798481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/1250000000000000000)
  centralHi := (193408156220933088241/100000000000000000000)
  directionLo := (199751084817161670577/100000000000000000000)
  directionHi := (99875542408580835289/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree017.table
  base := (-771759263280615926002682918085117446023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-35701090033020032351798863740374087000000000000)
      constant := (157952268811681374931776200844337103323094890833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree017.table
  base := (-784645095222720792740928591124936510037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-321654420131366150571570809731392783000000000000)
      constant := (1424400922275684858830203858472974681421759440843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199751084817161670577/100000000000000000000)
  centralHi := (99875542408580835289/50000000000000000000)
  directionLo := (102949352691608718171/50000000000000000000)
  directionHi := (205898705383217436343/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree018.table
  base := (-223959023337797677550711244493366190503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-18897212924654910722831245339544443500000000000)
      constant := (87498429056081493218198246539945960891192723652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree018.table
  base := (-901536872610869202664088236594675444741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-18917484091371725981971306284722443500000000000)
      constant := (87678010398163553839078981097566772271709611011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/50000000000000000000)
  centralHi := (205898705383217436343/100000000000000000000)
  directionLo := (211868019935376349211/100000000000000000000)
  directionHi := (52967004983844087303/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree019.table
  base := (-670454683020700031333600911378399896709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-19943880832799805269763058808901843500000000000)
      constant := (96711113420408444459869662493131746553464623878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree019.table
  base := (-2691887065889424345332005893978769514827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-359375007158015984779396216518615183000000000000)
      constant := (1744452772029237676611831240024405342271800725653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211868019935376349211/100000000000000000000)
  centralHi := (52967004983844087303/25000000000000000000)
  directionLo := (217673698145157370683/100000000000000000000)
  directionHi := (54418424536289342671/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree020.table
  base := (-216141359658463616129683703490300633801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-20990548740944699816694872278259243500000000000)
      constant := (106596666706695041944283167403327658589157906168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree020.table
  base := (-3467135190735650896159413538307417250089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-378235300671340901883308919912226383000000000000)
      constant := (1922831552377215057802495360640150185184475345271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/100000000000000000000)
  centralHi := (54418424536289342671/25000000000000000000)
  directionLo := (27916062764406227853/12500000000000000000)
  directionHi := (8933140084609992913/4000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree021.table
  base := (-4134264354690500986537129313299441769591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-899478230575085484229660642759863000000000000)
      constant := (4781249877371994428235868438768821052976039089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree021.table
  base := (-4142069808487662844875482418803026238071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-900443524228267163236330211577863000000000000)
      constant := (4791565414334600894189755760291028468854841009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27916062764406227853/12500000000000000000)
  centralHi := (8933140084609992913/4000000000000000000)
  directionLo := (228843616581046895971/100000000000000000000)
  directionHi := (57210904145261723993/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree022.table
  base := (-590103555400899544648002189131832873517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-23083884557234488910558499216974043500000000000)
      constant := (128330978793585740121947651908009041553077330028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree022.table
  base := (-4727682111877589411366758129628925544969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-415955887697990736091134326699448783000000000000)
      constant := (2314983359611061924093023145657579653163283901591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228843616581046895971/100000000000000000000)
  centralHi := (57210904145261723993/25000000000000000000)
  directionLo := (234228909067060420031/100000000000000000000)
  directionHi := (3659826704172819063/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree023.table
  base := (-5227107627902189612034426343741698161307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-48261104930758766914980625372662887000000000000)
      constant := (280315505340314617257631905950891685451862101597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree023.table
  base := (-5233115475451590816466193844709372040143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-434816181211315653195047030093059983000000000000)
      constant := (2528361069215151053824976503206838188903749932177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/100000000000000000000)
  centralHi := (3659826704172819063/1562500000000000000)
  directionLo := (47898627469102834941/20000000000000000000)
  directionHi := (119746568672757087353/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree024.table
  base := (-2830366466430322006207247392402599471907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-25177220373524278004422126155688843500000000000)
      constant := (152612619975157827950224904631302063576650194197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree024.table
  base := (-2832995573382351436599865413204228222349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-25204248595813365016608874082592843500000000000)
      constant := (152947991265600498668563908077268017210327208379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47898627469102834941/20000000000000000000)
  centralHi := (119746568672757087353/50000000000000000000)
  directionLo := (244644116684725066177/100000000000000000000)
  directionHi := (122322058342362533089/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree025.table
  base := (-6028074814857857268045056980679335776161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-52447776563338345102707879250092487000000000000)
      constant := (331377264080976037734959432160882076803567269831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree025.table
  base := (-6032670302366951682885541830978780054583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-472536768237965487402872436880282383000000000000)
      constant := (2988966786487973673703501883356563186336750423337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244644116684725066177/100000000000000000000)
  centralHi := (122322058342362533089/50000000000000000000)
  directionLo := (124844428010726044111/50000000000000000000)
  directionHi := (249688856021452088223/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree026.table
  base := (-6334456668293576319705809523785662879827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-54541112379628134196571506188807287000000000000)
      constant := (358759964593034277217188583918156733643433884517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree026.table
  base := (-3169233802740436594008112556330957390937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-245698530875645202253392570136946791500000000000)
      constant := (1617982776754569193162110849355629279685159375943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/50000000000000000000)
  centralHi := (249688856021452088223/100000000000000000000)
  directionLo := (254633669836008702103/100000000000000000000)
  directionHi := (31829208729501087763/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree027.table
  base := (-6584330262446767673013101127662405788243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-56634448195917923290435133127522087000000000000)
      constant := (387363629822706999825106536941731766063180036453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree027.table
  base := (-6587826685935917145942513953632463024649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-56695261696068369067855315963056087000000000000)
      constant := (388219210964251025177664166779772080570300491679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/100000000000000000000)
  centralHi := (31829208729501087763/12500000000000000000)
  directionLo := (64871067706935782903/25000000000000000000)
  directionHi := (259484270827743131613/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree028.table
  base := (-3390710341535150512719432594344611170869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-599263102165384820247946531288131500000000000)
      constant := (4256940136606090137555684100421800566061741251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree028.table
  base := (-1356893021334170251584071910796070964321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 801378000000000000000000000000000000000000000
      center := (8013780)
      previous := (4006890)
      next := (4006890)
      square := (73323705895680337346620447415280000000000000)
      linear := (-2159663872563021382508614477800473400000000000)
      constant := (15358840131645281517742002222801652321377182831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64871067706935782903/25000000000000000000)
  centralHi := (259484270827743131613/100000000000000000000)
  directionLo := (2113966778166318903/800000000000000000)
  directionHi := (66061461817697465719/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree029.table
  base := (-6928846506378345284692885470739133301789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-60821119828497501478162387004951687000000000000)
      constant := (448202672022653858500172881752352654767281544619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree029.table
  base := (-3465747272217333518364507346060009759217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-273988971145632577909261625227363591500000000000)
      constant := (2021366630158021832857362267303325987729865874863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2113966778166318903/800000000000000000)
  centralHi := (66061461817697465719/25000000000000000000)
  directionLo := (67230782009019899011/25000000000000000000)
  directionHi := (53784625607215919209/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree030.table
  base := (-7029219676252616166069087083677715678961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-62914455644787290572026013943666487000000000000)
      constant := (480425547697153739481584615523780421592591888631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree030.table
  base := (-439470041132374812025849687264875769279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-31491013100255004051246441880463243500000000000)
      constant := (240743001332400116908984642867639472623364419272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67230782009019899011/25000000000000000000)
  centralHi := (53784625607215919209/20000000000000000000)
  directionLo := (273520437601217867167/100000000000000000000)
  directionHi := (8547513675038058349/3125000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree031.table
  base := (-708472865090601257927708929829137584071/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-6500779146107707966588964088238128700000000000)
      constant := (51384398622583974927909232713744035765359175441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree031.table
  base := (-1771681553619322757441121813576199641573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-292849264658957495013174328620974791500000000000)
      constant := (2317397633666877202574330223163205310898140107894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273520437601217867167/100000000000000000000)
  centralHi := (8547513675038058349/3125000000000000000)
  directionLo := (2780417428704074537/1000000000000000000)
  directionHi := (278041742870407453701/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree032.table
  base := (-7097207705402949697355087419962387753909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-67101127277366868759753267821096087000000000000)
      constant := (548453986084464889324673175426977176205602653139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree032.table
  base := (-7098940361113822444180800929875437901833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-604558822831239907130261360635560783000000000000)
      constant := (4946961077320863444897986643913074068465069416087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/1000000000000000000)
  centralHi := (278041742870407453701/100000000000000000000)
  directionLo := (56498138649433693123/20000000000000000000)
  directionHi := (17655668327948029101/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree033.table
  base := (-3534097374327847726386750083605646589029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-34597231546828328926808447379905443500000000000)
      constant := (292126096140068844333936450157897739152282154659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree033.table
  base := (-7069696408329824068263042457614514078173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-69268790704951647137130451558796887000000000000)
      constant := (585537927699612927378674534728926032717557333483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56498138649433693123/20000000000000000000)
  centralHi := (17655668327948029101/6250000000000000000)
  directionLo := (286870655111529120253/100000000000000000000)
  directionHi := (143435327555764560127/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree034.table
  base := (-1749744898588765265890717007076388820369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-35643899454973223473740260849262843500000000000)
      constant := (310617895523443522801516277421532816646178471598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree034.table
  base := (-1400056012349999345336572329748077135539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39267522000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (3592861588888336529984401923348720000000000000)
      linear := (-128455881971577948267617353484556636600000000000)
      constant := (1120682168004752275598161375279806985711262667821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870655111529120253/100000000000000000000)
  centralHi := (143435327555764560127/50000000000000000000)
  directionLo := (291184741628008293203/100000000000000000000)
  directionHi := (72796185407002073301/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree035.table
  base := (-6890644287249637567817387485020032619087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-1497574178086453796762125482392663000000000000)
      constant := (13457192283116624715743051931675465627765627673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree035.table
  base := (-3445884854498703934680736392633339953613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-6746323503787904677979586436901983500000000000)
      constant := (60690289558140223216811859646799324647326760643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184741628008293203/100000000000000000000)
  centralHi := (72796185407002073301/25000000000000000000)
  directionLo := (295435838634756705829/100000000000000000000)
  directionHi := (29543583863475670583/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree036.table
  base := (-1348819362156686468425389485541462485371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-15094894108505205027041555115191057400000000000)
      constant := (139750020793081152620951821204362007285751087741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree036.table
  base := (-1349014017564853750599360035171395911781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-15111111041878657234353603871333457400000000000)
      constant := (140056359909192516558729338321107554247968306851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295435838634756705829/100000000000000000000)
  centralHi := (29543583863475670583/10000000000000000000)
  directionLo := (149813313612871252933/50000000000000000000)
  directionHi := (299626627225742505867/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree037.table
  base := (-6560099276227668053791073469448008445217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-77567806358815814229071402514670087000000000000)
      constant := (739277174757121102588909972141024157084514203207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree037.table
  base := (-6560940436825057309152623750769993665743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-698860290397864492649824877603616783000000000000)
      constant := (6668059390962419532048483202182257144395288050577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149813313612871252933/50000000000000000000)
  centralHi := (299626627225742505867/100000000000000000000)
  directionLo := (303759603528063154283/100000000000000000000)
  directionHi := (75939900882015788571/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree038.table
  base := (-6339291507367433214518149954222483334599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-79661142175105603322935029453384887000000000000)
      constant := (780982238453718569168003463020201041153555578129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree038.table
  base := (-1585004510866877121522474856641571403671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-358860291955594704876868790498613991500000000000)
      constant := (3522102724747090466389524102243149690791778126738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303759603528063154283/100000000000000000000)
  centralHi := (75939900882015788571/25000000000000000000)
  directionLo := (76959274022197194319/25000000000000000000)
  directionHi := (307837096088788777277/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree039.table
  base := (-304110539052600241722591713785080545207/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-8175447799139539241679865639209968700000000000)
      constant := (82386412297017043641537789588898326096590236994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree039.table
  base := (-6082837950180091346946620314244287384831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-81842319713834925206405587154537687000000000000)
      constant := (825662651845975780683663329400108551985657013401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76959274022197194319/25000000000000000000)
  centralHi := (307837096088788777277/100000000000000000000)
  directionLo := (77965320303817706413/25000000000000000000)
  directionHi := (311861281215270825653/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree040.table
  base := (-1157861671320703936483243004652546910321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-16769562761537036302132456666162897400000000000)
      constant := (173584368774235788525575445118215009991274339191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree040.table
  base := (-5789849451735173386718874548175982768243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-755441170937839243961562987784450383000000000000)
      constant := (7828325820975043599369326592161094488388198548077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77965320303817706413/25000000000000000000)
  centralHi := (311861281215270825653/100000000000000000000)
  directionLo := (78958549138963686213/25000000000000000000)
  directionHi := (315834196555854744853/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree041.table
  base := (-2730481660745293968061262294859406897839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-42970574811987485302262955134764643500000000000)
      constant := (456577287083218889056564622517907772679564184169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree041.table
  base := (-5461429911441883185203424268646339913853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-774301464451164161065475691178061583000000000000)
      constant := (8236283903516944052774119030730448406606649608867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78958549138963686213/25000000000000000000)
  centralHi := (315834196555854744853/100000000000000000000)
  directionLo := (159878876580784075139/50000000000000000000)
  directionHi := (319757753161568150279/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree042.table
  base := (-2548747096498522082774399102153155101639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-898311075921068976514178951104531500000000000)
      constant := (9791445091849543433933921847016364881719930081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree042.table
  base := (-5097896335887173747222021792593386473341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-1798552739148501311041697039845063000000000000)
      constant := (19625469138793468764971530947204265840820385339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159878876580784075139/50000000000000000000)
  centralHi := (319757753161568150279/100000000000000000000)
  directionLo := (323633746231425012737/100000000000000000000)
  directionHi := (161816873115712506369/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree043.table
  base := (-1174792160685081456316820912225673318359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-45063910628277274396126582073479443500000000000)
      constant := (503571197221117730576113486187544157472947218178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree043.table
  base := (-2349757537509130666520939792664410511543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-406011025738906997636650548982641991500000000000)
      constant := (4541982275798382305217452348720421147810476996777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323633746231425012737/100000000000000000000)
  centralHi := (161816873115712506369/50000000000000000000)
  directionLo := (163731932356396549113/50000000000000000000)
  directionHi := (327463864712793098227/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree044.table
  base := (-4266211650268990115986185162160340020203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-92221157072844337886116791085673687000000000000)
      constant := (1055896409689968807551733371053726133596066569613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree044.table
  base := (-170660398147503295573070978713620630361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7853504400000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (718572317777667305996880384669744000000000000)
      linear := (-33235293799645556495088552054355807320000000000)
      constant := (380947099726392804422400473537644636778822782279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163731932356396549113/50000000000000000000)
  centralHi := (327463864712793098227/100000000000000000000)
  directionLo := (16562484995124562987/5000000000000000000)
  directionHi := (331249699902491259741/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree045.table
  base := (-949703085374340499472553012120096263589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-47157246444567063489990209012194243500000000000)
      constant := (552911626080394272153988374169698155786377904838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree045.table
  base := (-949767272569973089442612479576952508659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-47207924361359101637840361375139243500000000000)
      constant := (554109278968093346185672343115112235741475280778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16562484995124562987/5000000000000000000)
  centralHi := (331249699902491259741/100000000000000000000)
  directionLo := (83748188293218683559/25000000000000000000)
  directionHi := (334992753172874734237/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree046.table
  base := (-412141215711016249092273961954768868729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-48203914352711958036922022481551643500000000000)
      constant := (578461287485688423896386545639836368598281973436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree046.table
  base := (-164867530798833122523831825551921111563/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-86860293201778874658503920814611758300000000000)
      constant := (1043483003168452131937435075702920478409435443114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83748188293218683559/25000000000000000000)
  centralHi := (334992753172874734237/100000000000000000000)
  directionLo := (338694442929308529497/100000000000000000000)
  directionHi := (169347221464654264749/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree047.table
  base := (-690324377410674719416951121050500204741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-49250582260856852583853835950909043500000000000)
      constant := (604597043218234478122029006565807244927703142022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree047.table
  base := (-276148747315395763554218807625253513623/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-88746322553111366368895191153972878300000000000)
      constant := (1090626391377750494295267132835819189549115773897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338694442929308529497/100000000000000000000)
  centralHi := (169347221464654264749/50000000000000000000)
  directionLo := (171178055445234195607/50000000000000000000)
  directionHi := (68471222178093678243/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree048.table
  base := (-2191428138522994036150232697371536748051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-100594500338003494261571298840532887000000000000)
      constant := (1262637541253683219741953009080135424809561050021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree048.table
  base := (-1095795721086306769782627047828635099153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-50351306613579921155159145274074443500000000000)
      constant := (632681470724207886756897254449603893500779855063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171178055445234195607/50000000000000000000)
  centralHi := (68471222178093678243/20000000000000000000)
  directionLo := (345979027770324175483/100000000000000000000)
  directionHi := (86494756942581043871/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree049.table
  base := (-198452023541123949625044565778382780989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1047835062798911054647295161012731500000000000)
      constant := (13441354419415642717981027370988452230830354924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree049.table
  base := (-99234782588973247223647949970490496821/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-9440651148548607121395686921703583500000000000)
      constant := (121233019019564186118974247972915452066554322648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345979027770324175483/100000000000000000000)
  centralHi := (86494756942581043871/25000000000000000000)
  directionLo := (349564398430032923511/100000000000000000000)
  directionHi := (43695549803754115439/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree050.table
  base := (-189988242936534771273634548314746515239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-20956234394116614489859710543592497400000000000)
      constant := (274607897686144357737616645331279074349357179569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree050.table
  base := (-950061765124317623368916318322301483873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-944044106071088415000690021720562383000000000000)
      constant := (12383970534290537639656515707042065911695692163647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349564398430032923511/100000000000000000000)
  centralHi := (43695549803754115439/12500000000000000000)
  directionLo := (353113366558960582019/100000000000000000000)
  directionHi := (17655668327948029101/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree051.table
  base := (-55694029109730578894421499365805695407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-21374901557374572308632435931335457400000000000)
      constant := (285999532246470782898606763798135580167104462697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree051.table
  base := (-139286833175306272305291015340874625499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-53494688865800740672477929173009643500000000000)
      constant := (716537176591462583087862564039474638119109792029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353113366558960582019/100000000000000000000)
  centralHi := (17655668327948029101/5000000000000000000)
  directionLo := (89156754734097025783/25000000000000000000)
  directionHi := (356627018936388103133/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree052.table
  base := (85348141740845076232769642453731052479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-21793568720632530127405161319078417400000000000)
      constant := (297625425732985345146639510961354744249183460391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree052.table
  base := (17066073657131749233285960054396795429/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7853504400000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (718572317777667305996880384669744000000000000)
      linear := (-39270587723909529968340617140311391320000000000)
      constant := (536877227952011586436924428993643435120618878469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89156754734097025783/25000000000000000000)
  centralHi := (356627018936388103133/100000000000000000000)
  directionLo := (180053194659458191969/50000000000000000000)
  directionHi := (360106389318916383939/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree053.table
  base := (1165643966391563346603066735194521071807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-111061179419452439730889433534106887000000000000)
      constant := (1547427787363921640144425586722861121859258052903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree053.table
  base := (145695962865985803261486275456898591153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-500312493305531583156214065950697991500000000000)
      constant := (6978377085440108592775643413371135977959738865732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180053194659458191969/50000000000000000000)
  centralHi := (360106389318916383939/100000000000000000000)
  directionLo := (181776230996491282981/50000000000000000000)
  directionHi := (363552461992982565963/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree054.table
  base := (969099877597432701875720612207860718841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-56577257617871114412376530236410843500000000000)
      constant := (803949775173359781171551637960974308686112487889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree054.table
  base := (484533582074386765078874234360030874361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-56638071118021560189796713071944843500000000000)
      constant := (805674378754913555583933374471009961586627755938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181776230996491282981/50000000000000000000)
  centralHi := (363552461992982565963/100000000000000000000)
  directionLo := (183483087513543799633/50000000000000000000)
  directionHi := (366966175027087599267/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree055.table
  base := (686093629801576114822934594301232304897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-57623925526016008959308343705768243500000000000)
      constant := (834771172205067223099086685877185382267739295026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree055.table
  base := (1372159202957891709925640666795508231247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-519172786818856500260126769344309191500000000000)
      constant := (7529041992446277602607727144589916889485836329967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183483087513543799633/50000000000000000000)
  centralHi := (366966175027087599267/100000000000000000000)
  directionLo := (46293552906773494711/12500000000000000000)
  directionHi := (370348423254187957689/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree056.table
  base := (896035004019921530711478844204941320337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1197359049676753132780411370920931500000000000)
      constant := (17677103142272133067422335233185330385045447154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree056.table
  base := (1792045952284486089128011602227488564689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-10787814970928958343103737164104383500000000000)
      constant := (159434582881983693666630982730739626165496670721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46293552906773494711/12500000000000000000)
  centralHi := (370348423254187957689/100000000000000000000)
  directionLo := (186850030505560263907/50000000000000000000)
  directionHi := (74740012202224105563/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree057.table
  base := (4457472473869964923076958222389104839417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-119434522684611596106343941288966087000000000000)
      constant := (1796340789085135842468709354399017072991228528593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree057.table
  base := (2228715617340521527924129901855042126557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-59781453370242379707115496970880043500000000000)
      constant := (900091875947882537092415433338024435195305765653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186850030505560263907/50000000000000000000)
  centralHi := (74740012202224105563/20000000000000000000)
  directionLo := (188510952329411925653/50000000000000000000)
  directionHi := (377021904658823851307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree058.table
  base := (5364351882036036435939380985591265809423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-121527858500901385200207568227680887000000000000)
      constant := (1861496344183959126789051351523209179509964747767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree058.table
  base := (5364316543145046355634720196522790354403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1094926454177687751831991648869451983000000000000)
      constant := (16789277528983849312426590466452934740871453799683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188510952329411925653/50000000000000000000)
  centralHi := (377021904658823851307/100000000000000000000)
  directionLo := (23769670931526254851/6250000000000000000)
  directionHi := (380314734904420077617/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree059.table
  base := (3152380697590881651493642700911859175933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-61810597158595587147035597583197843500000000000)
      constant := (963911368245209351716490861114729302486213941557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree059.table
  base := (3152365560199796590674967521302030147271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-556893373845506334467952176131531591500000000000)
      constant := (8693730040064379094600922144568952749726313616231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23769670931526254851/6250000000000000000)
  centralHi := (380314734904420077617/100000000000000000000)
  directionLo := (38357929894387076599/10000000000000000000)
  directionHi := (383579298943870765991/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree060.table
  base := (7278686831547624973369080217637180910299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-125714530133480963387934822105110487000000000000)
      constant := (1995319935066594907292721745502219391634063667171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree060.table
  base := (7278660901823084846381050010687890140841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-125849671244926398448868561739630487000000000000)
      constant := (1999577904928354808215374287407940062291058725889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38357929894387076599/10000000000000000000)
  centralHi := (383579298943870765991/100000000000000000000)
  directionLo := (2417601952761663603/625000000000000000)
  directionHi := (386816312441866176481/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree061.table
  base := (8286116251148007976479782441345552876203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-127807865949770752481798449043825287000000000000)
      constant := (2063987913865062862999356003400621552120470254387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree061.table
  base := (1035761756049305356687887531611295919999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-575753667358831251571864879525142791500000000000)
      constant := (9307750244609322118729704617998422914974141944956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2417601952761663603/625000000000000000)
  centralHi := (386816312441866176481/100000000000000000000)
  directionLo := (97506615340952473177/25000000000000000000)
  directionHi := (390026461363809892709/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree062.table
  base := (145734993763550018346485559294605469697/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-64950600883030270787831037991270043500000000000)
      constant := (1066913325477329553174699831889415388522484054816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree062.table
  base := (932702059398091484830054087620336864069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-117036762823098742024764246244389678300000000000)
      constant := (1924535791904644252576618413399996924328620233509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97506615340952473177/25000000000000000000)
  centralHi := (390026461363809892709/100000000000000000000)
  directionLo := (393210403673183027113/100000000000000000000)
  directionHi := (196605201836591513557/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree063.table
  base := (2600362103964010593812899668996100237707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1346883036554595210913527580829131500000000000)
      constant := (22498327835398670504051418861267389007365906694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree063.table
  base := (2600358037159211266567556573000391940517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1348330977034367729423531934056131500000000000)
      constant := (22546228196272562733095426571933737899167514714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393210403673183027113/100000000000000000000)
  centralHi := (196605201836591513557/50000000000000000000)
  directionLo := (396368770906184794313/100000000000000000000)
  directionHi := (198184385453092397157/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree064.table
  base := (11509335568273940420263106701209984222921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-134087873398640119763389329859969687000000000000)
      constant := (2277016329058703715150798551212995723671844626209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree064.table
  base := (1150932164899508197802347368838397030657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-120808821525763725445546786923111918300000000000)
      constant := (2053674640073605514355255366889993650123029210977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396368770906184794313/100000000000000000000)
  centralHi := (198184385453092397157/50000000000000000000)
  directionLo := (79900433926864668231/20000000000000000000)
  directionHi := (99875542408580835289/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree065.table
  base := (1581336881981303171723600182529560735909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-68090604607464954428626478399342243500000000000)
      constant := (1175183620714717013801464786634996554160587299444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree065.table
  base := (6325341574128831755461599335114029323179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-613474254385481085779690286312365191500000000000)
      constant := (10599138598579698531016062638306221594478288246219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79900433926864668231/20000000000000000000)
  centralHi := (99875542408580835289/25000000000000000000)
  directionLo := (402611182824550614729/100000000000000000000)
  directionHi := (40261118282455061473/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree066.table
  base := (1382552182394060965008959813641415971583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-13827454503121969795111658373739928700000000000)
      constant := (242488885395440623978340231461421517243071490407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree066.table
  base := (1728188954936084826833747774364369937573/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-69211600126904838259071848667685643500000000000)
      constant := (1215020308893191281452780182647858284342174756468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402611182824550614729/100000000000000000000)
  centralHi := (40261118282455061473/10000000000000000000)
  directionLo := (25356023194098695343/6250000000000000000)
  directionHi := (405696371105579125489/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree067.table
  base := (15033811615756938990895112370699246376831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-140367880847509487044980210676114087000000000000)
      constant := (2500581157347314855238726441925261542749201754599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree067.table
  base := (751690145345833702855598411961428670387/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-126466909579761200576720597941195278300000000000)
      constant := (2255301140671874401252356064518071894065852271014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25356023194098695343/6250000000000000000)
  centralHi := (405696371105579125489/100000000000000000000)
  directionLo := (408758273948170784141/100000000000000000000)
  directionHi := (204379136974085392071/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree068.table
  base := (16275560846306332964706800005810529758773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-142461216663799276138843837614828887000000000000)
      constant := (2577444143787393504208255367666242685174126303917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree068.table
  base := (16275553400797574106534575640528783278563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1283529389310936922871118682805563983000000000000)
      constant := (23246214667388473107070293142407874468512102365443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408758273948170784141/100000000000000000000)
  centralHi := (204379136974085392071/50000000000000000000)
  directionLo := (102949352691608718171/25000000000000000000)
  directionHi := (82359482153286974537/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree069.table
  base := (8775383248136599018162669294968935874847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-72277276240044532616353732276771843500000000000)
      constant := (1327738903343958829621369624564091840460119101063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree069.table
  base := (17550760132097706375856740009723643948131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-144709964758251315552781265133241687000000000000)
      constant := (2661108364822295289465554630389097049258522272299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102949352691608718171/25000000000000000000)
  centralHi := (82359482153286974537/20000000000000000000)
  directionLo := (5185178524331273399/1250000000000000000)
  directionHi := (414814281946501871921/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree070.table
  base := (18859426022686580868157309778129786231799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-2992814046864874578093287581474663000000000000)
      constant := (55809839602067804887317780693519201212825923279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree070.table
  base := (18859420583851880873889305312720578118579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (40068900)
      previous := (20034450)
      next := (20034450)
      square := (366618529478401686733102237076400000000000000)
      linear := (-26964285231379321573039675297811967000000000000)
      constant := (503352922557914377985225637614237435725755300931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5185178524331273399/1250000000000000000)
  centralHi := (414814281946501871921/100000000000000000000)
  directionLo := (417809369808342146587/100000000000000000000)
  directionHi := (104452342452085536647/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree071.table
  base := (631298040116004380402053737321479943889/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-74370612056334321710217359215486643500000000000)
      constant := (1407528570277567058100764198548664565378195620496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree071.table
  base := (20201532636551741430228757998090722073607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1340110269850911674182856792986397583000000000000)
      constant := (25389168391585993352775908992566141671510624245927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417809369808342146587/100000000000000000000)
  centralHi := (104452342452085536647/25000000000000000000)
  directionLo := (420783139505964596207/100000000000000000000)
  directionHi := (26298946219122787263/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree072.table
  base := (10788549237665967823376003349478806810111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-75417279964479216257149172684844043500000000000)
      constant := (1448301401456917618059411729826276493941654639719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree072.table
  base := (10788547252670025404957240291031146376149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-75498364631346477293709416465556043500000000000)
      constant := (1451366711505653538038779572989922157722813951821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420783139505964596207/100000000000000000000)
  centralHi := (26298946219122787263/6250000000000000000)
  directionLo := (423736039870752698423/100000000000000000000)
  directionHi := (52967004983844087303/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree073.table
  base := (11493054039015041383982721088641577857723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-76463947872624110804080986154201443500000000000)
      constant := (1489659562131278915592693971424606244452380598467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree073.table
  base := (22986104687139974444572088148869916655899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1377830856877561508390682199773619983000000000000)
      constant := (26870590422374064182490425374896863377711840206139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423736039870752698423/100000000000000000000)
  centralHi := (52967004983844087303/12500000000000000000)
  directionLo := (426668504202267287233/100000000000000000000)
  directionHi := (213334252101133643617/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree074.table
  base := (763392650371901868857898345360868214349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-77510615780769005351012799623558843500000000000)
      constant := (1531603050904575226087317930026164693096488953936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree074.table
  base := (24428561916145523670113838744596167555273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1396691150390886425494594903167231183000000000000)
      constant := (27627137212550362592353680167248047527296184371753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426668504202267287233/100000000000000000000)
  centralHi := (213334252101133643617/50000000000000000000)
  directionLo := (214790475505230582241/50000000000000000000)
  directionHi := (429580951010461164483/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree075.table
  base := (6476116899711726641850730945799933435897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-78557283688913899897944613092916243500000000000)
      constant := (1574131866600856221508887565806312197226957893026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree075.table
  base := (1619029070396819513134805375545816335167/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-78641746883567296811028200364491243500000000000)
      constant := (1577457842038940041175023107829456538310724242744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214790475505230582241/50000000000000000000)
  centralHi := (429580951010461164483/100000000000000000000)
  directionLo := (216236892356452609677/50000000000000000000)
  directionHi := (86494756942581043871/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree076.table
  base := (6853453882686575598402188578480358144439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-79603951597058794444876426562273643500000000000)
      constant := (1617246008229574749122887695663277015444959734462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree076.table
  base := (2741381341999222707465519851269603648971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-143441173741753625970242030995445358300000000000)
      constant := (2917190223719936254911867353587605601408624509931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216236892356452609677/50000000000000000000)
  centralHi := (86494756942581043871/20000000000000000000)
  directionLo := (217673698145157370683/50000000000000000000)
  directionHi := (435347396290314741367/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree077.table
  base := (28956607842644917318787944995964882319851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-3291862020620558734359520001291063000000000000)
      constant := (67793692855361061217836068988062046025762086371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree077.table
  base := (14478303020500930904008532293050056799619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-14829306438070012008227887891306783500000000000)
      constant := (305715514685725829683243960934370541208982537491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217673698145157370683/50000000000000000000)
  centralHi := (435347396290314741367/100000000000000000000)
  directionLo := (109550540975846054543/25000000000000000000)
  directionHi := (438202163903384218173/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree078.table
  base := (7633210972544960074517158812788668945087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-81697287413348583538740053500988443500000000000)
      constant := (1705230266078321785166771416871418324850213396046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree078.table
  base := (30532842352623933722806544311768737728291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-163570258271576232656693968526852887000000000000)
      constant := (3417655083356038838378751655651420498647660936939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109550540975846054543/25000000000000000000)
  centralHi := (438202163903384218173/100000000000000000000)
  directionLo := (220519226736842871537/50000000000000000000)
  directionHi := (17641538138947429723/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree079.table
  base := (251113461957542116991053873266324437801/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-82743955321493478085671866970345843500000000000)
      constant := (1750100381003450753870928695128493285256180974656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree079.table
  base := (4017815227323735225175256217820026252227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-745496308978755505507079210067643591500000000000)
      constant := (15784114079840024249818672338782404806799802542988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220519226736842871537/50000000000000000000)
  centralHi := (17641538138947429723/4000000000000000000)
  directionLo := (55482077403894657543/12500000000000000000)
  directionHi := (88771323846231452069/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree080.table
  base := (16892822553289494560561362430726830919603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-83790623229638372632603680439703243500000000000)
      constant := (1795555819233010746838325038759739452729210612987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree080.table
  base := (16892821993628888447057492297574640100203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-754926455735417964059035561764449191500000000000)
      constant := (16194058829380399238569864188911046083388401753483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55482077403894657543/12500000000000000000)
  centralHi := (88771323846231452069/20000000000000000000)
  directionLo := (446657004230499645649/100000000000000000000)
  directionHi := (8933140084609992913/2000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree081.table
  base := (17731104716536579024605071414804051389749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-84837291137783267179535493909060643500000000000)
      constant := (1841596580346896569233481172339611377174227746221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree081.table
  base := (35462208478257728480002412063760951370807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-169857022776017871691331536324723287000000000000)
      constant := (3690951582219834217314617431750215826483005223903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446657004230499645649/100000000000000000000)
  centralHi := (8933140084609992913/2000000000000000000)
  directionLo := (1123599852096534397/250000000000000000)
  directionHi := (449439940838613758801/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree082.table
  base := (37172215785614839078687322559810256283521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-171767918091856323452934614756836087000000000000)
      constant := (3776445327982456316042734791402968587579933283609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree082.table
  base := (37172214971245796083618216100331044110439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1547573498497485762325896530316120783000000000000)
      constant := (34059567897043620570619694790488403816944816931079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1123599852096534397/250000000000000000)
  centralHi := (449439940838613758801/100000000000000000000)
  directionLo := (45220575119503808983/10000000000000000000)
  directionHi := (452205751195038089831/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree083.table
  base := (38915663890916232868450707140288662813733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-173861253908146112546798241695550887000000000000)
      constant := (3870868139735825766795169116284536524799380137757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree083.table
  base := (1216114474888538704613422285203650511223/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-783216896005405339714904616854865991500000000000)
      constant := (17455564312329584328565102429206735064438083195248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45220575119503808983/10000000000000000000)
  centralHi := (452205751195038089831/100000000000000000000)
  directionLo := (454954747647192654327/100000000000000000000)
  directionHi := (56869343455899081791/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree084.table
  base := (40692553518774442755797853786161517228797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-3590909994376242890625752421107463000000000000)
      constant := (80948195825545044811644422898323798908543271237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree084.table
  base := (5086569115826329408835584661135106328213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1797385584494484803326215348189731500000000000)
      constant := (40559236302000200401732055544856300275353483892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454954747647192654327/100000000000000000000)
  centralHi := (56869343455899081791/12500000000000000000)
  directionLo := (457687233162093791943/100000000000000000000)
  directionHi := (57210904145261723993/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree085.table
  base := (42502884475281858192105200015477257935317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-178047925540725690734525495572980487000000000000)
      constant := (4063225694707085527236429396965268144526374159693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree085.table
  base := (5312860496303845762577200077909583840127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-802077189518730256818817320248477191500000000000)
      constant := (18322960637200889636865043095428867609906062910588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457687233162093791943/100000000000000000000)
  centralHi := (57210904145261723993/12500000000000000000)
  directionLo := (460403501716076074087/100000000000000000000)
  directionHi := (57550437714509509261/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree086.table
  base := (44346656597106814159554434801934753155581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-180141261357015479828389122511695287000000000000)
      constant := (4161160437145647997338070978891846837116741463349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree086.table
  base := (5543332020843933224520383163122419610281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-811507336275392715370773671945282791500000000000)
      constant := (18764576594804074727983967917462548275479881187364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460403501716076074087/100000000000000000000)
  centralHi := (57550437714509509261/12500000000000000000)
  directionLo := (463103838663940380997/100000000000000000000)
  directionHi := (231551919331970190499/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree087.table
  base := (46223869746675714730978233925884462820069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-182234597173305268922252749450410087000000000000)
      constant := (4260265822467273816926104062160034382791402305501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree087.table
  base := (11555967344967772248487773668224888670031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-91215275892450574880303335960232043500000000000)
      constant := (2134607897851052979370558758134555983310888114798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463103838663940380997/100000000000000000000)
  centralHi := (231551919331970190499/50000000000000000000)
  directionLo := (465788521088840250689/100000000000000000000)
  directionHi := (46578852108884025069/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree088.table
  base := (48134523808114457479124007440061032972693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-184327932989595058016116376389124887000000000000)
      constant := (4360541850419180271206506731474762941199885987597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree088.table
  base := (24067261747757834719112670906958164847603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-830367629788717632474686375338893991500000000000)
      constant := (19663644093645282024924433317911582237616438724883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465788521088840250689/100000000000000000000)
  centralHi := (46578852108884025069/10000000000000000000)
  directionLo := (234228909067060420031/50000000000000000000)
  directionHi := (468457818134120840063/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree089.table
  base := (10015723736765886504633872942630371569319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-37284253761176969421996000665567937400000000000)
      constant := (892397704157692814001915679564899150959244908751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree089.table
  base := (3129913651091195058786744493211770785891/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-839797776545380091026642727035699591500000000000)
      constant := (20121095632816850370657978781501408290975728528408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234228909067060420031/50000000000000000000)
  centralHi := (468457818134120840063/100000000000000000000)
  directionLo := (94222398263647077137/20000000000000000000)
  directionHi := (235555995659117692843/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree090.table
  base := (26028077145813631091007693204765860475413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-94257302311087318101921815133277243500000000000)
      constant := (2282302916697908988158024508404952840337067246477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree090.table
  base := (52056154064676570055766792403036326036031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-188717316289342788795244239718334487000000000000)
      constant := (4574183488306393411421290350500244613301056671399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94222398263647077137/20000000000000000000)
  centralHi := (235555995659117692843/50000000000000000000)
  directionLo := (236875647416891058639/50000000000000000000)
  directionHi := (473751294833782117279/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree091.table
  base := (13516782640572088835335293871230181774529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-1944978984065963523445992420461931500000000000)
      constant := (47636671307043239232060053430845733095567611218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree091.table
  base := (54067130368946689469555635402286871189019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (40068900)
      previous := (20034450)
      next := (20034450)
      square := (366618529478401686733102237076400000000000000)
      linear := (-35047268165661428903287976752216767000000000000)
      constant := (859258542312706993850733348368478686129856834091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236875647416891058639/50000000000000000000)
  centralHi := (473751294833782117279/100000000000000000000)
  directionLo := (476375975831629452117/100000000000000000000)
  directionHi := (238187987915814726059/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree092.table
  base := (56111547437522746690024032827032516603229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-192701276254754214391570884143984087000000000000)
      constant := (4773352384744561225551878865391697292912925557141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree092.table
  base := (5611154727283218579139466502703931553833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19633761000000000000000000000000000000000000000
      center := (196337610)
      previous := (98168805)
      next := (98168805)
      square := (1796430794444168264992200961674360000000000000)
      linear := (-173617643363073493336502356425223278300000000000)
      constant := (4305024280020129663808179001417252571488315755913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476375975831629452117/100000000000000000000)
  centralHi := (238187987915814726059/50000000000000000000)
  directionLo := (478986274691028349411/100000000000000000000)
  directionHi := (119746568672757087353/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree093.table
  base := (7273675608530996515281788460677721953213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-97397306035522001742717255541349443500000000000)
      constant := (2439740811625857249953873541362191907129483210708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree093.table
  base := (1163788094559575612155455643408983599933/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436305800000000000000000000000000000000000000
      center := (4363058)
      previous := (2181529)
      next := (2181529)
      square := (39920684320981516999826688037208000000000000)
      linear := (-3900081615875688556597636150324097740000000000)
      constant := (97794164609875835945068544213649586303778237557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478986274691028349411/100000000000000000000)
  centralHi := (119746568672757087353/25000000000000000000)
  directionLo := (120395606319136840193/25000000000000000000)
  directionHi := (481582425276547360773/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree094.table
  base := (15075175703284558028770565679759813342131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-98443973943666896289649069010706843500000000000)
      constant := (2493390751760771918850994435334529788180891396598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree094.table
  base := (30150351346841220740113207401638350364777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-886948510328692383786424485519727591500000000000)
      constant := (22487531197625979032825028867768220725496294436297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120395606319136840193/25000000000000000000)
  centralHi := (481582425276547360773/100000000000000000000)
  directionLo := (484164655182607665287/100000000000000000000)
  directionHi := (60520581897825958161/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree095.table
  base := (3122272061870104807014431766160374007791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-19898128370362358167316176496012848700000000000)
      constant := (509525202547815072428580858949500514347684584878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree095.table
  base := (1248908822713650992355771396615696097639/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3926752200000000000000000000000000000000000000
      center := (39267522)
      previous := (19633761)
      next := (19633761)
      square := (359286158888833652998440192334872000000000000)
      linear := (-35855146283414193693535233488661327660000000000)
      constant := (919066155239042550162709472620883810229676790279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484164655182607665287/100000000000000000000)
  centralHi := (60520581897825958161/12500000000000000000)
  directionLo := (243366592983170882861/50000000000000000000)
  directionHi := (486733185966341765723/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree096.table
  base := (64623620111752739993913003022150546521189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-201074619519913370767025391898843287000000000000)
      constant := (5204893189057645103340364662719063571601822917981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree096.table
  base := (32311810012572684244894721465374355837211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-100645422649113033432259687657037643500000000000)
      constant := (2607895009665473322830941804149235149115195075619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243366592983170882861/50000000000000000000)
  centralHi := (486733185966341765723/100000000000000000000)
  directionLo := (97857646673890026471/20000000000000000000)
  directionHi := (122322058342362533089/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree097.table
  base := (16708809852885095925371241611685084695363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-101583977668101579930444509418779043500000000000)
      constant := (2657852497103126382503865327237950088010781100054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree097.table
  base := (66835239337807800687319390313101769810169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1830477901197359518884587081220288783000000000000)
      constant := (47941469630854759118468243049693265163129873515609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97857646673890026471/20000000000000000000)
  centralHi := (122322058342362533089/25000000000000000000)
  directionLo := (15369687735302641873/3125000000000000000)
  directionHi := (491830007529684539937/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree098.table
  base := (69080299116021378229393917434801706354307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-4189005941887611203158217260740263000000000000)
      constant := (110769131446504506884801286701063125768600101947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree098.table
  base := (269844918176781857662407280343042508819/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-18870797905211065673352038618509183500000000000)
      constant := (499503940124286203136151316753296708056470565248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15369687735302641873/3125000000000000000)
  centralHi := (491830007529684539937/100000000000000000000)
  directionLo := (494358713182544814827/100000000000000000000)
  directionHi := (123589678295636203707/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree099.table
  base := (71358799207742415916684378170046005772843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-207354626968782738048616272714987687000000000000)
      constant := (5540840529036974423574665301782552183427624416947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree099.table
  base := (71358799154318637860777326152369158529019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-207577609802667705899156943111945687000000000000)
      constant := (5552428853068582139296252596232599436036652290051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494358713182544814827/100000000000000000000)
  centralHi := (123589678295636203707/25000000000000000000)
  directionLo := (49687454985373688961/10000000000000000000)
  directionHi := (496874549853736889611/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree100.table
  base := (36835369836010865659085255320411945054107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-104723981392536263571239949826851243500000000000)
      constant := (2827582129324492413288033299377780925081940989603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree100.table
  base := (73670739626553625855612317503232957607897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1887058781737334270196325191401122383000000000000)
      constant := (51002890266882789807952891683532604416996581410617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49687454985373688961/10000000000000000000)
  centralHi := (496874549853736889611/100000000000000000000)
  directionLo := (124844428010726044111/25000000000000000000)
  directionHi := (99875542408580835289/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree101.table
  base := (76016120496512016202509559678204541606377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-211541298601362316236343526592417287000000000000)
      constant := (5770658629687816035380854009930199684946018010433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree101.table
  base := (76016120457818635709284496797991881600407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-1905919075250659187300237894794733583000000000000)
      constant := (52044477899738296944604653775327647401282688540727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124844428010726044111/25000000000000000000)
  centralHi := (99875542408580835289/20000000000000000000)
  directionLo := (62733548674888883693/12500000000000000000)
  directionHi := (100373677879822213909/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree102.table
  base := (39197470835416089568644191203596902298961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-106817317208826052665103576765566043500000000000)
      constant := (2943661821065410698988783362071761281175350091369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree102.table
  base := (9799367704738406351850674078601891607527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-106932187153554672466897255454908043500000000000)
      constant := (2949812365332409462182973170227880025986707075132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62733548674888883693/12500000000000000000)
  centralHi := (100373677879822213909/20000000000000000000)
  directionLo := (504346766888526645779/100000000000000000000)
  directionHi := (25217338344426332289/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree103.table
  base := (80807203186257107455586590521423248008641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-215727970233941894424070780469846887000000000000)
      constant := (6005159295958966828055050573613926865305042592089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree103.table
  base := (5050450197390206310051165370513418367649/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-971819831138654510754031650790977991500000000000)
      constant := (27079662147724813727897195655046970505187444783112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504346766888526645779/100000000000000000000)
  centralHi := (25217338344426332289/5000000000000000000)
  directionLo := (63351628119341018271/12500000000000000000)
  directionHi := (506813024954728146169/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree104.table
  base := (83252905035456297258161674768697703482713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-217821306050231683517934407408561687000000000000)
      constant := (6124165591156260618772494946374980520380939408177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree104.table
  base := (41626452505811632916026316662710576708711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-981249977895316969305988002487783591500000000000)
      constant := (27616291528997818078939294404980124011270998392071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63351628119341018271/12500000000000000000)
  centralHi := (506813024954728146169/100000000000000000000)
  directionLo := (254633669836008702103/50000000000000000000)
  directionHi := (509267339672017404207/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree105.table
  base := (17146409442454731168639644508083632723987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (890420)
      previous := (445210)
      next := (445210)
      square := (8147078432853370816291160823920000000000000)
      linear := (-897610783128659071884889936111332600000000000)
      constant := (25487112357997032960711025172139016912504625227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree105.table
  base := (2679126474749978139396521073568784372823/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-2246440191954601877228898762323331500000000000)
      constant := (63850792362247907576964744784684088584999244528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254633669836008702103/50000000000000000000)
  centralHi := (509267339672017404207/100000000000000000000)
  directionLo := (511709882892118870873/100000000000000000000)
  directionHi := (255854941446059435437/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree106.table
  base := (88244629711541993001892024394456995585453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-222007977682811261705661661285991287000000000000)
      constant := (6365690105606731822571146797791087482122537697637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree106.table
  base := (3529785187771859155498510646387490978803/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7853504400000000000000000000000000000000000000
      center := (78535044)
      previous := (39267522)
      next := (39267522)
      square := (718572317777667305996880384669744000000000000)
      linear := (-80008821712691350912792056470511583320000000000)
      constant := (2296430868474841701897218176501260555587474168083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511709882892118870873/100000000000000000000)
  centralHi := (255854941446059435437/50000000000000000000)
  directionLo := (257070411192302558581/50000000000000000000)
  directionHi := (514140822384605117163/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree107.table
  base := (90790652528926738708907180466729402617793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-224101313499101050799525288224706087000000000000)
      constant := (6488208324839180870150530837931468493463391345497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree107.table
  base := (5674415782141178868063797699860955697419/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1009540418165304344961857057578200391500000000000)
      constant := (29257850801508620128989688217654265412157703702872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257070411192302558581/50000000000000000000)
  centralHi := (514140822384605117163/100000000000000000000)
  directionLo := (51656032197137453343/10000000000000000000)
  directionHi := (516560321971374533431/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree108.table
  base := (46685057830397142485298669382661400972441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-113097324657695419946694457581710443500000000000)
      constant := (3305948592699346698449790977490318556402008242289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree108.table
  base := (46685057824159922504993284667063264140439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-113218951657996311501534823252778443500000000000)
      constant := (3312843807603956764170626751767099363557027751231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51656032197137453343/10000000000000000000)
  centralHi := (516560321971374533431/100000000000000000000)
  directionLo := (20758741666219450529/4000000000000000000)
  directionHi := (259484270827743131613/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree109.table
  base := (95983019104101074322276789423384575992173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-228287985131680628987252542102135687000000000000)
      constant := (6736756687278629793945921796978468216179629172517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree109.table
  base := (11997877386686619927976440506616835594019/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1028400711678629262065769760971811591500000000000)
      constant := (30378616256687175711765881423295904705517048301836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20758741666219450529/4000000000000000000)
  centralHi := (259484270827743131613/50000000000000000000)
  directionLo := (260682818872319545701/50000000000000000000)
  directionHi := (521365637744639091403/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree110.table
  base := (49314681428150084021197298764966013570977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-115190660473985209040558084520425243500000000000)
      constant := (3431393415236716920303632037219770315119479883833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree110.table
  base := (49314681423639950744881920733348507792837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1037830858435291720617726112668617191500000000000)
      constant := (30946916766238789083386631315221095821711199169957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260682818872319545701/50000000000000000000)
  centralHi := (521365637744639091403/100000000000000000000)
  directionLo := (130937940742390986527/25000000000000000000)
  directionHi := (523751762969563946109/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree111.table
  base := (5065457345763127078147731281326191985741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-23247465676426020717497979597956528700000000000)
      constant := (698998761497846100804681274161027833002923155978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree111.table
  base := (5065457345379653754473476348487745493093/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-23272466782043426203770721430342728700000000000)
      constant := (700455462157110162461589979607290498075603358394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130937940742390986527/25000000000000000000)
  centralHi := (523751762969563946109/100000000000000000000)
  directionLo := (263063533298791887331/50000000000000000000)
  directionHi := (526127066597583774663/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree112.table
  base := (104022371279210787953064448922287549529207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-4787101889398979515690682100373063000000000000)
      constant := (145272633485506812887755611794470899992589824847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree112.table
  base := (52011185636345179459390823329599113373123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-21565125549971768116768139103310783500000000000)
      constant := (655088843860481187699210614694909531138363281747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263063533298791887331/50000000000000000000)
  centralHi := (526127066597583774663/100000000000000000000)
  directionLo := (528491694541579725751/100000000000000000000)
  directionHi := (66061461817697465719/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree113.table
  base := (106769035946663275498944058616179224604471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-236661328396839785362707049856994887000000000000)
      constant := (7247901107904320088415969994576195371172167016159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree113.table
  base := (106769035941120171515471203168933871735949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2132242597410558192547190335518067983000000000000)
      constant := (65366978845010803482210454195221657996468277774189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528491694541579725751/100000000000000000000)
  centralHi := (66061461817697465719/12500000000000000000)
  directionLo := (530845789464588733607/100000000000000000000)
  directionHi := (66355723683073591701/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree114.table
  base := (54774570458193556525188501960092449481659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-119377332106564787228285338397854843500000000000)
      constant := (3689306908159615095498303623940258412725274076611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree114.table
  base := (27387285227918802640663564600250676278281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-119505716162437950536172391050648843500000000000)
      constant := (3696989335231508444414560806925755129141364143298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530845789464588733607/100000000000000000000)
  centralHi := (66355723683073591701/12500000000000000000)
  directionLo := (106637898176048935881/20000000000000000000)
  directionHi := (266594745440122339703/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree115.table
  base := (56181343093679268003707747939339314241273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-120424000014709681775217151867212243500000000000)
      constant := (3755248583016165383538988618874730376107450046417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree115.table
  base := (22472537236670699777083382429107328430263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39267522000000000000000000000000000000000000000
      center := (392675220)
      previous := (196337610)
      next := (196337610)
      square := (3592861588888336529984401923348720000000000000)
      linear := (-433992636887441605351003148461058076600000000000)
      constant := (13547038853155305873179569303225707443748288909143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106637898176048935881/20000000000000000000)
  centralHi := (266594745440122339703/50000000000000000000)
  directionLo := (66940366906157904133/12500000000000000000)
  directionHi := (107104587049852646613/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree116.table
  base := (115209671758729544211973643126634710161501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-242941335845709152644297930673139287000000000000)
      constant := (7643551157041771879723211007679373994623909115029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree116.table
  base := (115209671755325585103278456730186576503419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2188823477950532943858928445698901583000000000000)
      constant := (68935137539822650331352231890066724016476344328859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66940366906157904133/12500000000000000000)
  centralHi := (107104587049852646613/20000000000000000000)
  directionLo := (537846256072159192089/100000000000000000000)
  directionHi := (53784625607215919209/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree117.table
  base := (59045048814899903507212887572783488652079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-122517335830999470869080778805927043500000000000)
      constant := (3888887894673012868655280659144866971965681248791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree117.table
  base := (2361801952538138569453786496968889274817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436305800000000000000000000000000000000000000
      center := (4363058)
      previous := (2181529)
      next := (2181529)
      square := (39920684320981516999826688037208000000000000)
      linear := (-4905963936586350802139646997983361740000000000)
      constant := (155879195236204610636603635889619466730802255193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537846256072159192089/100000000000000000000)
  centralHi := (53784625607215919209/10000000000000000000)
  directionLo := (540159583978374575907/100000000000000000000)
  directionHi := (135039895994593643977/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree118.table
  base := (60501981899996502910245831867442089002583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-123564003739144365416012592275284443500000000000)
      constant := (3956585531471917542056683308817166483479715889407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree118.table
  base := (121003963797534650407588759016045400055727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2226544064977182778066753852486123983000000000000)
      constant := (71366695215173751307625324452989626873843530599247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540159583978374575907/100000000000000000000)
  centralHi := (135039895994593643977/25000000000000000000)
  directionLo := (542463046811985851297/100000000000000000000)
  directionHi := (271231523405992925649/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree119.table
  base := (30987817567209228762631799766904999749131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-2543074931577331835978457260094731500000000000)
      constant := (82140173243205813738113178269861827237662122502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree119.table
  base := (3873477195835873875419580443513621365659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (20034450)
      previous := (10017225)
      next := (10017225)
      square := (183309264739200843366551118538200000000000000)
      linear := (-22912289372352119338476189345711583500000000000)
      constant := (740799077718965641990344553698544099902152624816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542463046811985851297/100000000000000000000)
  centralHi := (271231523405992925649/50000000000000000000)
  directionLo := (108951353942829881713/20000000000000000000)
  directionHi := (272378384857074704283/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree120.table
  base := (63466008517973316252621749190699813238801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-125657339555434154509876219213999243500000000000)
      constant := (4093736767008095024332911699801195742875028306729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree120.table
  base := (63466008517085850755450200831897544278701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-125792480666879589570809958848519243500000000000)
      constant := (4102248947785519647457957673592822737872770313829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108951353942829881713/20000000000000000000)
  centralHi := (272378384857074704283/50000000000000000000)
  directionLo := (109408175040487146867/20000000000000000000)
  directionHi := (8547513675038058349/1562500000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree121.table
  base := (129946204101010462866889477674978652651559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-253408014927158098113616065366713287000000000000)
      constant := (8326380731489216018730724200571979504640302853711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree121.table
  base := (129946204099502450860745707801596397286191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2283124945517157529378491962666957583000000000000)
      constant := (75093209546209956405730297570591134960778122694351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109408175040487146867/20000000000000000000)
  centralHi := (8547513675038058349/1562500000000000000)
  directionLo := (549315483247194594089/100000000000000000000)
  directionHi := (54931548324719459409/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree122.table
  base := (66496915731889018100560188187688838458997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-127750675371723943603739846152714043500000000000)
      constant := (4233229285126350733628646341083605973574617266413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree122.table
  base := (132993831462496889926372118443642391746567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2301985239030482446482404666060568783000000000000)
      constant := (76356495074665663840839119839017139485020469048487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549315483247194594089/100000000000000000000)
  centralHi := (54931548324719459409/10000000000000000000)
  directionLo := (275790355672542953947/50000000000000000000)
  directionHi := (110316142269017181579/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree123.table
  base := (1700936239050628864507247684647880631163/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2181529000000000000000000000000000000000000000
      center := (21815290)
      previous := (10907645)
      next := (10907645)
      square := (199603421604907584999133440186040000000000000)
      linear := (-25759468655973767630134331924414288700000000000)
      constant := (860770705030621217541101382871404062933363105816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree123.table
  base := (136074899122961971398048682176586786021473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-257871725838200818176257485494908887000000000000)
      constant := (8625593071722520634980972717288507740722637972217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275790355672542953947/50000000000000000000)
  centralHi := (110316142269017181579/20000000000000000000)
  directionLo := (553836674589903841277/100000000000000000000)
  directionHi := (276918337294951920639/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree124.table
  base := (34797351770417788015786006722769938335549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-129844011188013732697603473091428843500000000000)
      constant := (4375063085824703770881286931576295850614423748842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree124.table
  base := (69594703540373333181884079154600631586119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1169852913028566140345115036423895591500000000000)
      constant := (39457368629359028381068380613164186967010911363559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553836674589903841277/100000000000000000000)
  centralHi := (276918337294951920639/50000000000000000000)
  directionLo := (2780417428704074537/500000000000000000)
  directionHi := (556083485740814907401/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree125.table
  base := (142337355336520271757382913771498524838173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-261781358192317254489070573121572487000000000000)
      constant := (8893715934282025143313626633125205842891694706517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree125.table
  base := (71168677667867510229685288423825971508637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1179283059785228598897071388120701191500000000000)
      constant := (40104846957154750181245158167293223205193388293757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2780417428704074537/500000000000000000)
  centralHi := (556083485740814907401/100000000000000000000)
  directionLo := (558321255288124557061/100000000000000000000)
  directionHi := (279160627644062278531/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree126.table
  base := (145518743888507259569752519832263806310337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40735392164266854081455804119600000000000000)
      linear := (-5385197836910347828223146940005863000000000000)
      constant := (184458700779670770426958866668522569920742513577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree126.table
  base := (72759371943920157660735934672554211756147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20367696082133427040727902059800000000000000)
      linear := (-2695494799414718951131582176456931500000000000)
      constant := (92420870308702169964023158536596460061595420587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558321255288124557061/100000000000000000000)
  centralHi := (279160627644062278531/50000000000000000000)
  directionLo := (560550091516680791721/100000000000000000000)
  directionHi := (280275045758340395861/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree127.table
  base := (29746714547513317362115594460243791754279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4363058000000000000000000000000000000000000000
      center := (43630580)
      previous := (21815290)
      next := (21815290)
      square := (399206843209815169998266880372080000000000000)
      linear := (-53193605964979366535359565399800417400000000000)
      constant := (1836881476682958482369557925705204370081920512591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree127.table
  base := (148733572737000160744754481324554463706513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1963376100)
      previous := (981688050)
      next := (981688050)
      square := (17964307944441682649922009616743600000000000000)
      linear := (-2396286706597107032001968183028624783000000000000)
      constant := (82831278352614272445091143916697051157896850385393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560550091516680791721/100000000000000000000)
  centralHi := (280275045758340395861/50000000000000000000)
  directionLo := (562770100567017746509/100000000000000000000)
  directionHi := (56277010056701774651/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree128.table
  base := (4749432558864168696090407446552965387053/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-134030682820593310885330726968858443500000000000)
      constant := (4665754534957350636581803668681534112445637504592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree128.table
  base := (37995460470793092618383336675053265230397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (981688050)
      previous := (490844025)
      next := (490844025)
      square := (8982153972220841324961004808371800000000000000)
      linear := (-1207573500055215974552940443211117991500000000000)
      constant := (42078953067662773849048432559023007695606449266234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell118.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562770100567017746509/100000000000000000000)
  centralHi := (56277010056701774651/10000000000000000000)
  directionLo := (564981386494336931231/100000000000000000000)
  directionHi := (17655668327948029101/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree129.table
  base := (9703971957921248608244659800196688546467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (109076450)
      previous := (54538225)
      next := (54538225)
      square := (998017108024537924995667200930200000000000000)
      linear := (-135077350728738205432262540438215843500000000000)
      constant := (4739890698851766935553606717423738591894684864344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree129.table
  base := (155263551326331497747694399676161732142789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (218152900)
      previous := (109076450)
      next := (109076450)
      square := (1996034216049075849991334401860400000000000000)
      linear := (-270445254847084096245532621090649687000000000000)
      constant := (9499454551156515561297698392527728185359726344381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell118.Kernel129
