import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell042.Parameters
import ForestUnimodality.BinomialMassData.Q23_48.Batch000_049
import ForestUnimodality.BinomialMassData.Q23_48.Batch050_099
import ForestUnimodality.BinomialMassData.Q23_48.Batch100_149
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch000_049
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch050_099
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree000.table
  base := (239536417093438226638646425449/5000000000000000000000000000)
  polynomial :=
    { denominator := 625000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (60629145046531170148984557500000000000)
      linear := (2675031726308033596349600375000000000)
      constant := (29942052136679778329830803181125000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree000.table
  base := (239536417093438226638646425449/5000000000000000000000000000)
  polynomial :=
    { denominator := 625000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (60629145046531170148984557500000000000)
      linear := (2675031726308033596349600375000000000)
      constant := (29942052136679778329830803181125000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree001.table
  base := (281754622851464685293064375304106659599011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-7981617447832944642685526481000000000000)
      constant := (2537611579582167850132482057243428686391099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree001.table
  base := (1406018358954566221903818057263391974971/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5880625000000000000000000000000000000000000
      center := (56454)
      previous := (28227)
      next := (28227)
      square := (570459625742811779931795701517500000000000)
      linear := (-523052618623381481072535069358578125000000)
      constant := (165484952937789149174646455323175184139675175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24978289183920414279/50000000000000000000)
  directionHi := (49956578367840828559/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree002.table
  base := (171063375942383739929383663404190129100833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-16348439464254246123245395416000000000000)
      constant := (1547219433535626897980359933515336161907497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree002.table
  base := (170447376577209786725645013272617055266891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-17140393772153524004049976458328500000000000)
      constant := (1611781974263181042879116466541314896443677419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24978289183920414279/50000000000000000000)
  centralHi := (49956578367840828559/100000000000000000000)
  directionLo := (2207789708048589889/3125000000000000000)
  directionHi := (70649270657554876449/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree003.table
  base := (53991378970855210575133787033462023227471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-1373070082259752644655848019500000000000)
      constant := (54962891660053136595301167595321398227471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree003.table
  base := (107458786524171694388001669563406162789217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-25911945646332944310939391806919750000000000)
      constant := (1029465849178802939982059923862215872793117753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2207789708048589889/3125000000000000000)
  centralHi := (70649270657554876449/100000000000000000000)
  directionLo := (86527331905396613047/100000000000000000000)
  directionHi := (10815916488174576631/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree004.table
  base := (4449997101385200158216952376588572543791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-2067630218568553067772820830375000000000)
      constant := (42008380723288924657466342715172152894119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree004.table
  base := (17698869607346157839069091865280902453887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-8670874380128091154457201788877750000000000)
      constant := (174764777959993897642607960324215690876122783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86527331905396613047/100000000000000000000)
  centralHi := (10815916488174576631/12500000000000000000)
  directionLo := (24978289183920414279/25000000000000000000)
  directionHi := (99913156735681657117/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree005.table
  base := (24531308937199494106176419811626629876289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-20724452756759075282462501110500000000000)
      constant := (245377226313269021323352496394249043886601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree005.table
  base := (24380657371759823755324312605850627602271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-21727524697345892462359111252051125000000000)
      constant := (255256402022531451483420653010614214289455339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24978289183920414279/25000000000000000000)
  centralHi := (99913156735681657117/100000000000000000000)
  directionLo := (27926576288446896627/25000000000000000000)
  directionHi := (111706305153787586509/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree006.table
  base := (8792296464652171587764112505780157223999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (24)
      previous := (12)
      next := (12)
      square := (242516580186124680595938230000000000000)
      linear := (-1383770209164984779041246421000000000000)
      constant := (10766084707900566014456894033811407223999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree006.table
  base := (8736341166307336135792171066699728107153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-13056650317217801307901909463173375000000000)
      constant := (100876619471046801622947259963495013244577577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27926576288446896627/25000000000000000000)
  centralHi := (111706305153787586509/100000000000000000000)
  directionLo := (3059203157414252757/2500000000000000000)
  directionHi := (122368126296570110281/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree007.table
  base := (13000201562657037075612856095419562938679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-29091274773180376763022370045500000000000)
      constant := (165467296050482895486741923710635441448111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree007.table
  base := (25831081996129414405468363358298461702337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-60998153143050625538497053201284750000000000)
      constant := (344952950176750546718178825243394247641663833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3059203157414252757/2500000000000000000)
  centralHi := (122368126296570110281/100000000000000000000)
  directionLo := (132172682713015837293/100000000000000000000)
  directionHi := (66086341356507918647/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree008.table
  base := (19608237700609927657945395782980075167667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-66549371562782055006604609026000000000000)
      constant := (303288792711027270411574906309820676509003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree008.table
  base := (389522082836658204625711411082604193841/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-34884852508615022922693234274938000000000000)
      constant := (158288265636083070290675319600313633996249225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132172682713015837293/100000000000000000000)
  centralHi := (66086341356507918647/50000000000000000000)
  directionLo := (141298541315109752897/100000000000000000000)
  directionHi := (70649270657554876449/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree009.table
  base := (14904753145859577301026428567793934164837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-8324021508800372943018275329000000000000)
      constant := (32761135929652754300335523533012684164837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree009.table
  base := (7398911558248796179945759962563362650223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-39270628445704733076137941949233625000000000)
      constant := (154095481315822177556753667459071377418135707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141298541315109752897/100000000000000000000)
  centralHi := (70649270657554876449/50000000000000000000)
  directionLo := (74934867551761242837/50000000000000000000)
  directionHi := (5994789404140899427/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree010.table
  base := (2818595376796504076876509241025486386177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-20820753898906164491931086724000000000000)
      constant := (75019693120903821222788325413135627475593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree010.table
  base := (5592380483026715808803971101229599087237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-43656404382794443229582649623529250000000000)
      constant := (157021424092670142909755038422765215780562933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74934867551761242837/50000000000000000000)
  centralHi := (5994789404140899427/4000000000000000000)
  directionLo := (3949414293776849247/2500000000000000000)
  directionHi := (157976571751073969881/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree011.table
  base := (8362121497961759632394225931004018672383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-91649837612045959448284215831000000000000)
      constant := (315779428481601393571065720508004918051447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree011.table
  base := (8284767044406368353371559103929068089733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-96084360639768306766054714595649750000000000)
      constant := (330818802504154925442504479625584045015672797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3949414293776849247/2500000000000000000)
  centralHi := (157976571751073969881/100000000000000000000)
  directionLo := (10355451641007074449/6250000000000000000)
  directionHi := (33137445251222638237/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree012.table
  base := (595768715223078103266710131800342578139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-5556481090470403384935782487000000000000)
      constant := (18892200981512715475307884500501712890695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree012.table
  base := (5889429914319486168043430539603079823043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-104855912513947727072944129944241000000000000)
      constant := (356557882375126127582992255952121596805011587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10355451641007074449/6250000000000000000)
  centralHi := (33137445251222638237/20000000000000000000)
  directionLo := (34610932762158645219/20000000000000000000)
  directionHi := (10815916488174576631/6250000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree013.table
  base := (1966000346736821387692596493053488655609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-54191740822444281204701976850500000000000)
      constant := (185878820025911400124063335952340772900481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree013.table
  base := (1935427867873272839065179046821092203437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-56813732194063573689916772646416125000000000)
      constant := (195028367328629412940842950965256737596826233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34610932762158645219/20000000000000000000)
  centralHi := (10815916488174576631/6250000000000000000)
  directionLo := (180121004851985235889/100000000000000000000)
  directionHi := (18012100485198523589/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree014.table
  base := (2202259149282674935673874643878778084487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-116750303661309863889963822636000000000000)
      constant := (410128268883714129324948336572034002760383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree014.table
  base := (107348332787183493064465079330087320663/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-30599754065576641921680740160355875000000000)
      constant := (107635772208051020358839938128091276359965835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180121004851985235889/100000000000000000000)
  centralHi := (18012100485198523589/10000000000000000000)
  directionLo := (11682525029248932783/6250000000000000000)
  directionHi := (186920400467982924529/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree015.table
  base := (712615686749339237828664948909935878793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-13901902853081240596724854619000000000000)
      constant := (50518764740747335700518509214378685878793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree015.table
  base := (662349025917429124846305717562671806111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-131170568136485987993612375990014750000000000)
      constant := (477495557882228115206544562271328731758073399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11682525029248932783/6250000000000000000)
  centralHi := (186920400467982924529/100000000000000000000)
  directionLo := (3023140563314894201/1562500000000000000)
  directionHi := (38696199210430645773/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree016.table
  base := (-144147848295029151020082840532027575933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-33370986923538116712770890126500000000000)
      constant := (126255631527343676403478088401711751816603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree016.table
  base := (-311202636681938083668769589485267849931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-69971060005332704150250895669303000000000000)
      constant := (265271675404858132659404665082378614799999221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3023140563314894201/1562500000000000000)
  centralHi := (38696199210430645773/20000000000000000000)
  directionLo := (199826313471363314233/100000000000000000000)
  directionHi := (99913156735681657117/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree017.table
  base := (-211864747448405300585855921873779715459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-17731346213821721041455428680125000000000)
      constant := (70115399526240779240122756354069576310869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree017.table
  base := (-1736705852280821296830061857136134885931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-148713671884844828607391206687197250000000000)
      constant := (589409752592479498947882355444963722092650221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199826313471363314233/100000000000000000000)
  centralHi := (99913156735681657117/50000000000000000000)
  directionLo := (41195249861010809399/20000000000000000000)
  directionHi := (51494062326263511749/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree018.table
  base := (-2665307504212403326444636613662447486861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-16690843525221674423578144264000000000000)
      constant := (69129378009190813307087988098962552513139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree018.table
  base := (-675853040164718872718938944259542106477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-39371305939756062228570155508947125000000000)
      constant := (163469919666777494033655049786457317929532907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41195249861010809399/20000000000000000000)
  centralHi := (51494062326263511749/25000000000000000000)
  directionLo := (42389562394532925869/20000000000000000000)
  directionHi := (105973905986332314673/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree019.table
  base := (-7012299543842547191395704115578472827/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-39646103435854092823190791827750000000000)
      constant := (172145158870989223776311125741091405569625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree019.table
  base := (-3540865088933423680782741341870769878397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-166256775633203669221170037384379750000000000)
      constant := (723780559595501160060344756393700275823537627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42389562394532925869/20000000000000000000)
  centralHi := (105973905986332314673/50000000000000000000)
  directionLo := (108877838335244126739/50000000000000000000)
  directionHi := (217755676670488253479/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree020.table
  base := (-4232536229188254687461419752813412865727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-166951235759837672773323036246000000000000)
      constant := (760036073395375346670205546644679284208457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree020.table
  base := (-4264126196565887727456715818941689205947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-175028327507383089528059452732971000000000000)
      constant := (798970681164680532435794321600478115011244677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108877838335244126739/50000000000000000000)
  centralHi := (217755676670488253479/100000000000000000000)
  directionLo := (27926576288446896627/12500000000000000000)
  directionHi := (223412610307575173017/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree021.table
  base := (-971411709793724593373795176012202992911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-19479784197362108250431433909000000000000)
      constant := (92935265640041687463608033144407735035445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree021.table
  base := (-977153422877087136445242413556410101811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-183799879381562509834948868081562250000000000)
      constant := (879331756900176451066018729090834442619676505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27926576288446896627/12500000000000000000)
  centralHi := (223412610307575173017/100000000000000000000)
  directionLo := (28616225228953008551/12500000000000000000)
  directionHi := (228929801831624068409/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree022.table
  base := (-269517109855070961101396536997043801313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-45921219948170068933610693529000000000000)
      constant := (229407239596601262379769516306414278940915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree022.table
  base := (-5416398032135173644247911311111797636053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-192571431255741930141838283430153500000000000)
      constant := (964763955526696030664052765240197306979877323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28616225228953008551/12500000000000000000)
  centralHi := (228929801831624068409/100000000000000000000)
  directionLo := (117158561241687422073/50000000000000000000)
  directionHi := (234317122483374844147/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree023.table
  base := (-5841421702999157971313441386675248806103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-192051701809101577215002643051000000000000)
      constant := (1003589465508752303044646433934641510745073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree023.table
  base := (-5865040288528134561555787672839953961683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-201342983129921350448727698778744750000000000)
      constant := (1055182395268288344221844767516706707158899653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117158561241687422073/50000000000000000000)
  centralHi := (234317122483374844147/100000000000000000000)
  directionLo := (239583333333333333333/100000000000000000000)
  directionHi := (119791666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree024.table
  base := (-1554504438207963010764869527466420178569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (24)
      previous := (12)
      next := (12)
      square := (242516580186124680595938230000000000000)
      linear := (-5567181217375635519321180888500000000000)
      constant := (30395261831996856452615879772783579821431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree024.table
  base := (-6239402148696269312889748729392282930711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-210114535004100770755617114127336000000000000)
      constant := (1150514549058326865921330945533772634904940201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239583333333333333333/100000000000000000000)
  centralHi := (119791666666666666667/50000000000000000000)
  directionLo := (244736252593140220561/100000000000000000000)
  directionHi := (122368126296570110281/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree025.table
  base := (-6526750551947670188852121662177056111181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-208785345841944180176122380921000000000000)
      constant := (1189489257867675118503379052108375244999371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree025.table
  base := (-6546091602163156866290734666004869094281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-218886086878280191062506529475927250000000000)
      constant := (1250698242323384241252214093088508770676285071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244736252593140220561/100000000000000000000)
  centralHi := (122368126296570110281/50000000000000000000)
  directionLo := (249782891839204142791/100000000000000000000)
  directionHi := (31222861479900517849/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree026.table
  base := (-6773309676198109024934132424844802609981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-217152167858365481656682249856000000000000)
      constant := (1289317755073453692126083731368021776510171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree026.table
  base := (-679078604405648404019350964581758276109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-113828819376229805684697972412259250000000000)
      constant := (677840028226352032469920757084966037369202095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249782891839204142791/100000000000000000000)
  centralHi := (31222861479900517849/12500000000000000000)
  directionLo := (254729567929947578313/100000000000000000000)
  directionHi := (127364783964973789157/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree027.table
  base := (-6962592674042211636608771432952371226341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-25057665541642975904138013199000000000000)
      constant := (154852315514787907266061817809266378773659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree027.table
  base := (-3489185449311966397810481983532559488063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-118214595313319515838142680086554875000000000)
      constant := (732707012244769948706474416980976150706502733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254729567929947578313/100000000000000000000)
  centralHi := (127364783964973789157/50000000000000000000)
  directionLo := (259581995716189839143/100000000000000000000)
  directionHi := (32447749464523729893/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree028.table
  base := (-1419764033702356670365703889741081304077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-233885811891208084617801987726000000000000)
      constant := (1502510525939301290357224611994651341316535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree028.table
  base := (-3556527411166330358564030652278509344079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-122600371250409225991587387760850500000000000)
      constant := (789930273592596126479229199624143239956560689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259581995716189839143/100000000000000000000)
  centralHi := (32447749464523729893/12500000000000000000)
  directionLo := (264345365426031674587/100000000000000000000)
  directionHi := (66086341356507918647/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree029.table
  base := (-1437126519492601992270757836391177624613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-242252633907629386098361856661000000000000)
      constant := (1615804050051378394897244772113115756892415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree029.table
  base := (-1799616641491743219318454630798563629281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-63493073593749468072516047717573062500000000)
      constant := (424746370405882901287165605086770339714438821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264345365426031674587/100000000000000000000)
  centralHi := (66086341356507918647/25000000000000000000)
  directionLo := (269024407711353291707/100000000000000000000)
  directionHi := (67256101927838322927/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree030.table
  base := (-7226172177861293471964868463067189611627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-27846606213783409730991302844000000000000)
      constant := (192613681335181540105954916685057810388373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree030.table
  base := (-904717131557669081333856230852103436671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-32842980781147161574619200777360437500000000)
      constant := (227844921118833424988978851253278296069050061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269024407711353291707/100000000000000000000)
  centralHi := (67256101927838322927/25000000000000000000)
  directionLo := (136811724339205178613/50000000000000000000)
  directionHi := (273623448678410357227/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree031.table
  base := (-7223152722153238019693591558875492508011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-258986277940471989059481594531000000000000)
      constant := (1855643347523048251301986537750339317427901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree031.table
  base := (-3616784643059698644157784407117696373389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-135757699061678356451921510783737375000000000)
      constant := (975578388299553545356669156649526027439970399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136811724339205178613/50000000000000000000)
  centralHi := (273623448678410357227/100000000000000000000)
  directionLo := (139073228362694673667/50000000000000000000)
  directionHi := (55629291345077869467/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree032.table
  base := (-7178919317179128615023599400405157162157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-267353099956893290540041463466000000000000)
      constant := (1982143590789059000848068866488353585540587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree032.table
  base := (-3594149050060192671063229325027872144137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-140143474998768066605366218458033000000000000)
      constant := (1042077868061733422829091960752621250995814967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139073228362694673667/50000000000000000000)
  centralHi := (55629291345077869467/20000000000000000000)
  directionLo := (141298541315109752897/50000000000000000000)
  directionHi := (56519416526043901159/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree033.table
  base := (-443468716089244670447957964922785245749/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (60629145046531170148984557500000000000)
      linear := (-1914721680370240222365287030562500000000)
      constant := (14673650099751844197006453592497136629251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree033.table
  base := (-7103941335004703699790624031907887704683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-289058501871715553517621852264657250000000000)
      constant := (2221737261662102164520119666732976987321012653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141298541315109752897/50000000000000000000)
  centralHi := (56519416526043901159/20000000000000000000)
  directionLo := (286978694040748142319/100000000000000000000)
  directionHi := (3587233675509351779/1250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree034.table
  base := (-871830865735955428225734389250943762851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-35510842998716986687645150167000000000000)
      constant := (281026704275221939779679749410444631134341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree034.table
  base := (-1745560936066993710938073545488098597923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-74457513436473743456127816903312125000000000)
      constant := (590971234207343183840456949057736673651517493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286978694040748142319/100000000000000000000)
  centralHi := (3587233675509351779/1250000000000000000)
  directionLo := (29129440529394922719/10000000000000000000)
  directionHi := (291294405293949227191/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree035.table
  base := (-6817879492668171241922512787326578077601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-292453566006157194981721070271000000000000)
      constant := (2387753990370600153674745467129529547301591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree035.table
  base := (-1706178675195936845005132745916102956331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-76650401405018598532850170740459937500000000)
      constant := (627646139983977834837342261684383490311225371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29129440529394922719/10000000000000000000)
  centralHi := (291294405293949227191/100000000000000000000)
  directionLo := (36943387914351842479/12500000000000000000)
  directionHi := (295547103314814739833/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree036.table
  base := (-6626511328221461621210566455959785580301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-33424487558064277384697882134000000000000)
      constant := (281290539481852422185512422098040214419699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree036.table
  base := (-6632660604412026598481501527667980661477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-315373157494253814438290098310431000000000000)
      constant := (2661823839065435186710204472097057188706162907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36943387914351842479/12500000000000000000)
  centralHi := (295547103314814739833/100000000000000000000)
  directionLo := (299739470207044971349/100000000000000000000)
  directionHi := (5994789404140899427/2000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree037.table
  base := (-6401680889100899502250812004918436571733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-309187210038999797942840808141000000000000)
      constant := (2679785982991009991774810007576952820854403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree037.table
  base := (-640721275193874077518983889665438270463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-162072354684216617372589756829511125000000000)
      constant := (1408796064923242739147468014817237053245755665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299739470207044971349/100000000000000000000)
  centralHi := (5994789404140899427/2000000000000000000)
  directionLo := (151937001518904392111/50000000000000000000)
  directionHi := (303874003037808784223/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree038.table
  base := (-6144374920419391065876489324574891129059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-317554032055421099423400677076000000000000)
      constant := (2832258492627598574362840934199950979838469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree038.table
  base := (-19216722863312021503936892067744475971/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5880625000000000000000000000000000000000000
      center := (56454)
      previous := (28227)
      next := (28227)
      square := (570459625742811779931795701517500000000000)
      linear := (-20807266327663290940754308062975843750000000)
      constant := (186117513114517759685146851543783240507870970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151937001518904392111/50000000000000000000)
  centralHi := (303874003037808784223/100000000000000000000)
  directionLo := (61590606246227011609/20000000000000000000)
  directionHi := (153976515615567529023/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree039.table
  base := (-1463862281120372255001611157372444151149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (24)
      previous := (12)
      next := (12)
      square := (242516580186124680595938230000000000000)
      linear := (-9053357057551177802887792944750000000000)
      constant := (83028463414602682585067637856119743348851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree039.table
  base := (-2929962993285189367989323402063987587263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-170843906558396037679479172178102375000000000)
      constant := (1571340042148597571753385781809973264033629933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61590606246227011609/20000000000000000000)
  centralHi := (153976515615567529023/50000000000000000000)
  directionLo := (311978731913998693121/100000000000000000000)
  directionHi := (155989365956999346561/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree040.table
  base := (-691955745679019129333832465396875457669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-41785959511032962798065051868250000000000)
      constant := (393759733963499918855415282150803120880979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree040.table
  base := (-2769836870623956671597579149258229490311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-175229682495485747832923879852398000000000000)
      constant := (1655992409505831910949494265356963381225663801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311978731913998693121/100000000000000000000)
  centralHi := (155989365956999346561/50000000000000000000)
  directionLo := (3949414293776849247/1250000000000000000)
  directionHi := (315953143502147939761/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree041.table
  base := (-2592805006158569621595677575153236472561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-171327249052342501932540141940500000000000)
      constant := (1657706128926547551252801416228105246746951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree041.table
  base := (-5189234157285838659100857577169847727467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-359230916865150915972737175053387250000000000)
      constant := (3485788396195759402859194536579915674216637997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3949414293776849247/1250000000000000000)
  centralHi := (315953143502147939761/100000000000000000000)
  directionLo := (319878177766335150027/100000000000000000000)
  directionHi := (79969544441583787507/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree042.table
  base := (-4805901165557300763511727040836421326823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-39002368902345145038404461424000000000000)
      constant := (387224755806355127776420880377788578673177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree042.table
  base := (-4809162602410105200610354780178517631757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-368002468739330336279626590401978500000000000)
      constant := (3664085590394548417973740014409802913540298387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319878177766335150027/100000000000000000000)
  centralHi := (79969544441583787507/25000000000000000000)
  directionLo := (64751126116333554723/20000000000000000000)
  directionHi := (20234726911354235851/6250000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree043.table
  base := (-4397006062853784998326188215171588472481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-359388142137527606826200021751000000000000)
      constant := (3658905125180992166665627814654424453747671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree043.table
  base := (-175997664270177413324620399491413046793/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-376774020613509756586516005750569750000000000)
      constant := (3846871861482002673506652952713287934427491575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64751126116333554723/20000000000000000000)
  centralHi := (20234726911354235851/6250000000000000000)
  directionLo := (40948398941448926393/12500000000000000000)
  directionHi := (65517438306318282229/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree044.table
  base := (-3959347918648280506518468617681255370647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-367754964153948908306759890686000000000000)
      constant := (3837055417694507955509168936719868701664177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree044.table
  base := (-1980995334426449982434824960127460479163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-192772786243844588446702710549580500000000000)
      constant := (2017071631198207548141088900182643583726555333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40948398941448926393/12500000000000000000)
  centralHi := (65517438306318282229/20000000000000000000)
  directionLo := (331374452512226382369/100000000000000000000)
  directionHi := (33137445251222638237/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree045.table
  base := (-3493295015387948146472595889309704374813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-41791309574485578865257751069000000000000)
      constant := (446607818361746563199217226758659045625187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree045.table
  base := (-3495674714654581891818184573994535465183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-394317124361868597200294836447752250000000000)
      constant := (4225896359549530766273264194723718452917468153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331374452512226382369/100000000000000000000)
  centralHi := (33137445251222638237/10000000000000000000)
  directionLo := (13404756618454510381/4000000000000000000)
  directionHi := (167559457730681379763/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree046.table
  base := (-2999168034096612344716451011997860583139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-384488608186791511267879628556000000000000)
      constant := (4206147081735411086678235198141144254751749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree046.table
  base := (-600262279474837222160618391587307807193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-403088676236048017507184251796343500000000000)
      constant := (4422128164142252524164625964697832627648105315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13404756618454510381/4000000000000000000)
  centralHi := (167559457730681379763/50000000000000000000)
  directionLo := (84705499829638505527/25000000000000000000)
  directionHi := (338821999318554022109/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree047.table
  base := (-2477246385383435375405900782151394991841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-392855430203212812748439497491000000000000)
      constant := (4397083052438101548697606607491856195073431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree047.table
  base := (-123958869975499109203876118828849921093/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-102965057027556859453518416786233687500000000)
      constant := (1155709018217238537911255804768156549895773565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84705499829638505527/25000000000000000000)
  centralHi := (338821999318554022109/100000000000000000000)
  directionLo := (342485046307783260629/100000000000000000000)
  directionHi := (34248504630778326063/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree048.table
  base := (-963886839697191345341563915776851682677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-22290125123313006346055520357000000000000)
      constant := (255126449159582042543432756955223148317323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree048.table
  base := (-385902775129525532321516678428509777093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-420631779984406858120963082493526000000000000)
      constant := (4828017816706139196826824851795108757536659815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342485046307783260629/100000000000000000000)
  centralHi := (34248504630778326063/10000000000000000000)
  directionLo := (346109327621586452191/100000000000000000000)
  directionHi := (10815916488174576631/3125000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree049.table
  base := (-337740613448028711772477840064164521049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-102397268559013853927389808840250000000000)
      constant := (1197931066549893198230477059611789706810559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree049.table
  base := (-676265577591161040967910990217056913169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-214701665929293139213926248921058625000000000)
      constant := (2518835708332264113625942019184984706621180379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346109327621586452191/100000000000000000000)
  centralHi := (10815916488174576631/3125000000000000000)
  directionLo := (87424012143721449977/25000000000000000000)
  directionHi := (349696048574885799909/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree050.table
  base := (-373499131088833605557137160496186076281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-208977948126238358595059552148000000000000)
      constant := (2497712963218490155909785120338346825313471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree050.table
  base := (-748412807369563220535005492930197853691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-438174883732765698734741913190708500000000000)
      constant := (5251795145540996264350777510787146916832121381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87424012143721449977/25000000000000000000)
  centralHi := (349696048574885799909/100000000000000000000)
  directionLo := (176623176643887191121/50000000000000000000)
  directionHi := (353246353287774382243/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree051.table
  base := (-116043211050404916470723832497565753367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-47369190918766446518964330359000000000000)
      constant := (578153289625133892919038340868221184246633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree051.table
  base := (-58659578380608326256255096068471541197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-223473217803472559520815664269649875000000000)
      constant := (2735193747420917402463659982896360488573564927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176623176643887191121/50000000000000000000)
  centralHi := (353246353287774382243/100000000000000000000)
  directionLo := (22297583059301703907/6250000000000000000)
  directionHi := (356761328948827262513/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree052.table
  base := (541760978894071876257800765232398293233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-434689540285319320151238842166000000000000)
      constant := (5415584031280986564831986265799091584639097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree052.table
  base := (108121935047880209848234007901314433729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-455717987481124539348520743887891000000000000)
      constant := (5693447146164760043347184746446822306284780805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22297583059301703907/6250000000000000000)
  centralHi := (356761328948827262513/100000000000000000000)
  directionLo := (180121004851985235889/50000000000000000000)
  directionHi := (360242009703970471779/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree053.table
  base := (1226290321892273062388404793326718470289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-443056362301740621631798711101000000000000)
      constant := (5632038084529453486559347782522159216232601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree053.table
  base := (153156392193943051749059114723114245197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5880625000000000000000000000000000000000000
      center := (56454)
      previous := (28227)
      next := (28227)
      square := (570459625742811779931795701517500000000000)
      linear := (-29030596209706497478463134952280140625000000)
      constant := (370060809151665827842264985326079242895240224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180121004851985235889/50000000000000000000)
  centralHi := (360242009703970471779/100000000000000000000)
  directionLo := (181844690105167614279/50000000000000000000)
  directionHi := (363689380210335228559/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree054.table
  base := (1937436270508541729489680302663970094257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-50158131590906880345817620004000000000000)
      constant := (650304532160520543249060771826788970094257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree054.table
  base := (1936497969256719001879686111105374456267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-473261091229483379962299574585073500000000000)
      constant := (6152963886409532297129826170776101929196516203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181844690105167614279/50000000000000000000)
  centralHi := (363689380210335228559/100000000000000000000)
  directionLo := (183552189444855165421/50000000000000000000)
  directionHi := (367104378889710330843/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree055.table
  base := (167193982808755815372228690534972325249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-28736875395911451537057403060687500000000)
      constant := (379855705633028481837133127709609672802241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree055.table
  base := (2674256223847922081031504649940137496327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-482032643103662800269188989933664750000000000)
      constant := (6389419082170712809603766854665037212687315743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183552189444855165421/50000000000000000000)
  centralHi := (367104378889710330843/100000000000000000000)
  directionLo := (74097580182411415161/20000000000000000000)
  directionHi := (185243950456028537903/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree056.table
  base := (429901163322344009779398422152509099249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-58519603543875565759184789738250000000000)
      constant := (788361104521661546576892086296997581893241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree056.table
  base := (859610889085137646415729608847977927549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-122701048744460555144019601320564000000000000)
      constant := (1657584439731558663163022664215887280570308541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74097580182411415161/20000000000000000000)
  centralHi := (185243950456028537903/50000000000000000000)
  directionLo := (373840800935965849057/100000000000000000000)
  directionHi := (186920400467982924529/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree057.table
  base := (2114839929970926930349511525741382322531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-26473536131523657086335454824500000000000)
      constant := (363351820509991716345216872631850757322531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree057.table
  base := (4228987737462086560394103835992258128541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-499575746852021640882967820630847250000000000)
      constant := (6875719237070872704832628816823151115715817269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373840800935965849057/100000000000000000000)
  centralHi := (186920400467982924529/50000000000000000000)
  directionLo := (94290973907456628129/25000000000000000000)
  directionHi := (377163895629826512517/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree058.table
  base := (2523225576021211248693434802895460920009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-242445236191923564517299027888000000000000)
      constant := (3389011255525624245563394213077871648280081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree058.table
  base := (1261456341023291713429478990696543931189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-127086824681550265297464308994859625000000000)
      constant := (1781390730011169219563212652070916397082932301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94290973907456628129/25000000000000000000)
  centralHi := (377163895629826512517/100000000000000000000)
  directionLo := (38045796599478488103/10000000000000000000)
  directionHi := (380457965994784881031/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree059.table
  base := (2944733371266503978424813187162412655759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-246628647200134215257578962355500000000000)
      constant := (3509978776912179056535374470365446088901831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree059.table
  base := (5888900739393264763822740547587137911059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-517118850600380481496746651328029750000000000)
      constant := (7379868283796074657175410552595725511464529131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38045796599478488103/10000000000000000000)
  centralHi := (380457965994784881031/100000000000000000000)
  directionLo := (383723759508205474257/100000000000000000000)
  directionHi := (191861879754102737129/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree060.table
  base := (3379338500813131251319770269880962294963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-27868006467593873999762099647000000000000)
      constant := (403674302823949646134319748652380962294963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree060.table
  base := (1689541224927064448182114876710937087141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-131472600618639975450909016669155250000000000)
      constant := (1909658716906511100754203429677798949240409669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383723759508205474257/100000000000000000000)
  centralHi := (191861879754102737129/50000000000000000000)
  directionLo := (3023140563314894201/781250000000000000)
  directionHi := (386961992104306457729/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree061.table
  base := (7654038255952427061691729246122507290637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-509990938433111033476277662581000000000000)
      constant := (7516561809011127211510224085487821315615733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree061.table
  base := (7653574768508935685936030083244688052507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-534661954348739322110525482025212250000000000)
      constant := (7901862266227522776492478613326534244495413363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3023140563314894201/781250000000000000)
  centralHi := (386961992104306457729/100000000000000000000)
  directionLo := (3048229296928392289/781250000000000000)
  directionHi := (390173350006834212993/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree062.table
  base := (1715102409046281329863483642312998883537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-518357760449532334956837531516000000000000)
      constant := (7771230282221938001485955801429209949759165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree062.table
  base := (8575092420321332617017725419013002968391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-543433506222918742417414897373803500000000000)
      constant := (8169550122759725233141546754436917493367090919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3048229296928392289/781250000000000000)
  centralHi := (390173350006834212993/100000000000000000000)
  directionLo := (393358491427066790577/100000000000000000000)
  directionHi := (196679245713533395289/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree063.table
  base := (9523064474976867530726961638714330937391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-58524953607328181826377488939000000000000)
      constant := (892238062823683221859093756821183080937391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree063.table
  base := (4761342219971842282335652305387609161729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-276102529048549081362152156361197375000000000)
      constant := (4220849061409509187643792678691252259719895661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393358491427066790577/100000000000000000000)
  centralHi := (196679245713533395289/50000000000000000000)
  directionLo := (396518048139047511881/100000000000000000000)
  directionHi := (198259024069523755941/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree064.table
  base := (10496665652464854662717091583972001348447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-535091404482374937917957269386000000000000)
      constant := (8293298389550244601859058703879748012136023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree064.table
  base := (5248160682127022542233143175602088356627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-280488304985638791515596864035493000000000000)
      constant := (4359152994593443904417474011771327049347503443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396518048139047511881/100000000000000000000)
  centralHi := (198259024069523755941/50000000000000000000)
  directionLo := (199826313471363314233/50000000000000000000)
  directionHi := (399652626942726628467/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree065.table
  base := (2874072298733840848148294737833852658067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-135864556624699059849629284580250000000000)
      constant := (2140174379297096193748337204258121861422603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree065.table
  base := (11495977195642814329935076029311191535507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-569748161845457003338083143419577250000000000)
      constant := (8999373477251824808828221155222573678891960363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199826313471363314233/50000000000000000000)
  centralHi := (399652626942726628467/100000000000000000000)
  directionLo := (20138140551230421659/5000000000000000000)
  directionHi := (402762811024608433181/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree066.table
  base := (6260955900245609868870763704416507404637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-30656947139734307826615389292000000000000)
      constant := (490685541033916386127288382436729007404637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree066.table
  base := (12521628977594846255029009090168850625737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-578519713719636423644972558768168500000000000)
      constant := (9284900371015978366120132867624951238975059433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20138140551230421659/5000000000000000000)
  centralHi := (402762811024608433181/100000000000000000000)
  directionLo := (405849161224544933353/100000000000000000000)
  directionHi := (202924580612272466677/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree067.table
  base := (13573512873448118070868548268006916792253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-560191870531638842359636876191000000000000)
      constant := (9108224868455416377106942606169531001130277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree067.table
  base := (13573256424230043843508470903955067647537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-587291265593815843951861974116759750000000000)
      constant := (9574886479609502647884884626697790768605050633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405849161224544933353/100000000000000000000)
  centralHi := (202924580612272466677/50000000000000000000)
  directionLo := (204456108608234599311/50000000000000000000)
  directionHi := (408912217216469198623/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree068.table
  base := (14651074197001581963143179135638276375719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-568558692548060143840196745126000000000000)
      constant := (9388352742771908767581124422418744487381471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree068.table
  base := (7325420798359158428009906114925942618117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-298031408733997632129375694732675500000000000)
      constant := (4934665817122972667530198973367118053468862853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204456108608234599311/50000000000000000000)
  centralHi := (408912217216469198623/100000000000000000000)
  directionLo := (41195249861010809399/10000000000000000000)
  directionHi := (411952498610108093991/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree069.table
  base := (3938644911758933432442447571846417888451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (24)
      previous := (12)
      next := (12)
      square := (242516580186124680595938230000000000000)
      linear := (-16025708737902262370021017057250000000000)
      constant := (268686756012303589515293768474713605388451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree069.table
  base := (3938592155109815552808869218874948587771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-151208592335543671141410201203485562500000000)
      constant := (2542058921390250763763615462880094158352181089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41195249861010809399/10000000000000000000)
  centralHi := (411952498610108093991/100000000000000000000)
  directionLo := (2593565662375271989/625000000000000000)
  directionHi := (414970505980043518241/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree070.table
  base := (16884014941726370661940799875629056784217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-585292336580902746801316482996000000000000)
      constant := (9961336160932059917636028097553786511057953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree070.table
  base := (4220955859395058072803302691791749530347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-153401480304088526218132555040633375000000000)
      constant := (2617899625321179151607464418119117467815409923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2593565662375271989/625000000000000000)
  centralHi := (414970505980043518241/100000000000000000000)
  directionLo := (417966721827893321523/100000000000000000000)
  directionHi := (104491680456973330381/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree071.table
  base := (9019683711152622534172079265559233138849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-296829579298662024140938175965500000000000)
      constant := (5127095731155193311807836637743892473249641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree071.table
  base := (2254899198822109378149144239604120718101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5880625000000000000000000000000000000000000
      center := (56454)
      previous := (28227)
      next := (28227)
      square := (570459625742811779931795701517500000000000)
      linear := (-38898592068158345323713727219445296875000000)
      constant := (673713747762741437534550367935951915386079592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417966721827893321523/100000000000000000000)
  centralHi := (104491680456973330381/25000000000000000000)
  directionLo := (26308850717678061363/6250000000000000000)
  directionHi := (420941611482848981809/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree072.table
  base := (1922062586096935384929507514149251957263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-33445887811874741653468678937000000000000)
      constant := (586182723307093461810686004382246259786315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree072.table
  base := (9610234016206738759518959712891604813419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-315574512482356472743154525429858000000000000)
      constant := (5545849985188535697401183910843327172189459371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26308850717678061363/6250000000000000000)
  centralHi := (420941611482848981809/100000000000000000000)
  directionLo := (423895623945329258691/100000000000000000000)
  directionHi := (105973905986332314673/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree073.table
  base := (10213890146225988437164196354195879636271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-305196401315083325621498044900500000000000)
      constant := (5426314371448273251695933047373247291726439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree073.table
  base := (10213818480165013125487417881011694971159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-319960288419446182896599233104153625000000000)
      constant := (5704219213785086410976092205083103111225822531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423895623945329258691/100000000000000000000)
  centralHi := (105973905986332314673/25000000000000000000)
  directionLo := (213414596339040398719/50000000000000000000)
  directionHi := (426829192678080797439/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree074.table
  base := (21660821866232782370812577834131872823501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-618759624646587952723555958736000000000000)
      constant := (11158210552762296210060543522506811855411509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree074.table
  base := (21660691669940417188194847424460067298881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-648692128713071786100087881556898500000000000)
      constant := (11729635253883598429157555249204098109152671329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213414596339040398719/50000000000000000000)
  centralHi := (426829192678080797439/100000000000000000000)
  directionLo := (429742736348672267403/100000000000000000000)
  directionHi := (107435684087168066851/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree075.table
  base := (22919742716762535082347474806767662031259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-69680716295889917133790647519000000000000)
      constant := (1274226042037220923921197662305986412031259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree075.table
  base := (11459812213580842534373655026293351761509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-328731840293625603203488648452744875000000000)
      constant := (6027645188273680798134393363006161993403725681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429742736348672267403/100000000000000000000)
  centralHi := (107435684087168066851/25000000000000000000)
  directionLo := (216318329763491532619/50000000000000000000)
  directionHi := (432636659526983065239/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree076.table
  base := (24204535849422394900504671231386888758011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-635493268679430555684675696606000000000000)
      constant := (11782100156663053258106716697933481998822099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree076.table
  base := (24204428355696050409184894186783254926127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-666235232461430626713866712254081000000000000)
      constant := (12385403730862376516126122917705318864349928943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216318329763491532619/50000000000000000000)
  centralHi := (432636659526983065239/100000000000000000000)
  directionLo := (435511353340976506957/100000000000000000000)
  directionHi := (217755676670488253479/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree077.table
  base := (25515195040235875481605780489342007135847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-643860090695851857165235565541000000000000)
      constant := (12100407831730702661415251254477796814222623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree077.table
  base := (25515097338103382618329307126815193846991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-675006784335610047020756127602672250000000000)
      constant := (12719975259269648999997167268266576071015713319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435511353340976506957/100000000000000000000)
  centralHi := (217755676670488253479/50000000000000000000)
  directionLo := (109591799023441733281/25000000000000000000)
  directionHi := (701387513750027093/160000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree078.table
  base := (26851714747609608349771233013921057577331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-72469656968030350960643937164000000000000)
      constant := (1380328594851510689881496278254046057577331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree078.table
  base := (26851625928757693869797853848467076068657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-683778336209789467327645542951263500000000000)
      constant := (13059004910531284128423485000213252492167493713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109591799023441733281/25000000000000000000)
  centralHi := (701387513750027093/160000000000000000)
  directionLo := (44120455384473688967/10000000000000000000)
  directionHi := (441204553844736889671/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree079.table
  base := (28214090034602606490744291613530434193941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-660593734728694460126355303411000000000000)
      constant := (12749748678029265017533051812634992657745469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree079.table
  base := (28214009277202971465519023990249646345963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-692549888083968887634534958299854750000000000)
      constant := (13402492639009341277928921272554095725203540867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44120455384473688967/10000000000000000000)
  centralHi := (441204553844736889671/100000000000000000000)
  directionLo := (222011890478615781929/50000000000000000000)
  directionHi := (444023780957231563859/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree080.table
  base := (29602316500417459396509099508684115077333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-668960556745115761606915172346000000000000)
      constant := (13080781765220532392641864468508157035695997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree080.table
  base := (29602243060615725925727584988566048169233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-701321439958148307941424373648446000000000000)
      constant := (13750438404030374235998365012098222947224313297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222011890478615781929/50000000000000000000)
  centralHi := (444023780957231563859/100000000000000000000)
  directionLo := (446825220615150346033/100000000000000000000)
  directionHi := (223412610307575173017/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree081.table
  base := (31016390219974881420374638783545891887847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-75258597640170784787497226809000000000000)
      constant := (1490672953323520529271076145629264641887847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree081.table
  base := (7754080856062030993011327053621103057543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-177523247958081932062078447249259312500000000)
      constant := (3525710542331265159828888866419003549977015837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446825220615150346033/100000000000000000000)
  centralHi := (223412610307575173017/50000000000000000000)
  directionLo := (1756285958244404129/390625000000000000)
  directionHi := (17984368212422698281/4000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree082.table
  base := (32456307690578777004780630054956527651027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-685694200777958364568034910216000000000000)
      constant := (13755573090578457269908471824652233748859243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree082.table
  base := (32456246928869974248884485663595825441643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-718864543706507148555203204345628500000000000)
      constant := (14459703902533683617415767888673986020017918987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1756285958244404129/390625000000000000)
  centralHi := (17984368212422698281/4000000000000000000)
  directionLo := (9047521146086860011/2000000000000000000)
  directionHi := (452376057304343000551/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree083.table
  base := (6784413156961099181508467004453076406709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-694061022794379666048594779151000000000000)
      constant := (14099331269074037059868561365768857188301905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree083.table
  base := (33922010504353140586090535302205835855909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-727636095580686568862092619694219750000000000)
      constant := (14821023574769407537074017818737107309177622781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9047521146086860011/2000000000000000000)
  centralHi := (452376057304343000551/100000000000000000000)
  directionLo := (455126089061530776629/100000000000000000000)
  directionHi := (45512608906153077663/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree084.table
  base := (35413661708860828929950451986741156651663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-78047538312311218614350516454000000000000)
      constant := (1605259010028252916725730024302741156651663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree084.table
  base := (35413611408650759308291299598365479264207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-736407647454865989168982035042811000000000000)
      constant := (15186801160232313457968728625647270263146923663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455126089061530776629/100000000000000000000)
  centralHi := (45512608906153077663/10000000000000000000)
  directionLo := (28616225228953008551/6250000000000000000)
  directionHi := (457859603663248136817/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree085.table
  base := (92327732414359454582799500962293998337/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-44424666676701391813107157313812500000000)
      constant := (924973283227885368359220734903029821500825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree085.table
  base := (36931047191518163084024792811688470457857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-745179199329045409475871450391402250000000000)
      constant := (15557036635868049305178174485573180324397351513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28616225228953008551/6250000000000000000)
  centralHi := (457859603663248136817/100000000000000000000)
  directionLo := (57572111899568083231/12500000000000000000)
  directionHi := (460576895196544665849/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree086.table
  base := (38474357322639196090599504407259026604803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-719161488843643570490274385956000000000000)
      constant := (15156055573154369562778388102654456239443227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree086.table
  base := (38474315662404586616633320426748308420773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-753950751203224829782760865739993500000000000)
      constant := (15931729981065722928026103150819189544868553157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57572111899568083231/12500000000000000000)
  centralHi := (460576895196544665849/100000000000000000000)
  directionLo := (231639124561844642147/50000000000000000000)
  directionHi := (92655649824737856859/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree087.table
  base := (40043452782033528731272149222631231827107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-80836478984451652441203806099000000000000)
      constant := (1724086688533473930098231390873599981827107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree087.table
  base := (2502713428876012969619681326241499797149/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-95340287884675531261206285136073093750000000)
      constant := (2038860147173792343953035772506460428680796757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231639124561844642147/50000000000000000000)
  centralHi := (92655649824737856859/20000000000000000000)
  directionLo := (116490985658047092229/25000000000000000000)
  directionHi := (465963942632188368917/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree088.table
  base := (20819188778055500203967455674772048557159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-367947566438243086725697061913000000000000)
      constant := (7940873193248255651969894796369448437014431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree088.table
  base := (10409585759278322508271731690408460897691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-192873463737895917599134924109294000000000000)
      constant := (4173622552086416025592220502639605364836374619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116490985658047092229/25000000000000000000)
  centralHi := (465963942632188368917/100000000000000000000)
  directionLo := (468634244966749688293/100000000000000000000)
  directionHi := (234317122483374844147/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree089.table
  base := (10814782511010528767668859598258317815239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-186065488723226868732988498190250000000000)
      constant := (4062738531958160474374074538932317047837151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree089.table
  base := (21629549309079192755399901603829648506861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-390132703412881545351714555892883625000000000)
      constant := (8541278529581960562893217156928728829793242649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468634244966749688293/100000000000000000000)
  centralHi := (234317122483374844147/50000000000000000000)
  directionLo := (235644708872158732467/50000000000000000000)
  directionHi := (94257883548863492987/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree090.table
  base := (22452854405912160507855222653862611040587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-41812709828296043134028547872000000000000)
      constant := (923577967105757454789975480079175111040587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree090.table
  base := (22452840099739884049660142646500557328103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-394518479349971255505159263567179250000000000)
      constant := (8737540858309572276687810492625489349368871127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235644708872158732467/50000000000000000000)
  centralHi := (94257883548863492987/20000000000000000000)
  directionLo := (473929715253221909641/100000000000000000000)
  directionHi := (236964857626610954821/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree091.table
  base := (46578112574376250526909284822922565742191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-760995598925750077893073730631000000000000)
      constant := (17002094215143755860664395224390271841679719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree091.table
  base := (23289043260827734882003435234200784899181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-398904255287060965658603971241474875000000000)
      constant := (8936032084430716543949250063626509313046081529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473929715253221909641/100000000000000000000)
  centralHi := (236964857626610954821/50000000000000000000)
  directionLo := (476555384737411420871/100000000000000000000)
  directionHi := (59569423092176427609/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree092.table
  base := (6034542522452918375166108176299255414641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-96170302617771422421704199945750000000000)
      constant := (2173003317398041988925540010108818298731769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree092.table
  base := (48276316455859221143097744012796298327691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-806580062448301351624097357831541000000000000)
      constant := (18273504405269660360930254825153082839715244619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476555384737411420871/100000000000000000000)
  centralHi := (59569423092176427609/12500000000000000000)
  directionLo := (239583333333333333333/50000000000000000000)
  directionHi := (479166666666666666667/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree093.table
  base := (25000195297172229558459275002891750803783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-43207180164366260047455192694500000000000)
      constant := (987233353929243554252270970960376125803783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree093.table
  base := (25000184494970496926327495497469609607601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-407675807161240385965493386590066125000000000)
      constant := (9339701208160253377703206618681538481602605309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239583333333333333333/50000000000000000000)
  centralHi := (479166666666666666667/100000000000000000000)
  directionLo := (240881897496816199973/50000000000000000000)
  directionHi := (481763794993632399947/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree094.table
  base := (1293756572289418813149267883583368958787/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-98262008121876747791844167179500000000000)
      constant := (2270076962678404318368087350530892228145415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree094.table
  base := (51750243216042271248928272557669377350303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-824123166196660192237876188528723500000000000)
      constant := (19089758193471931488225928425575973569926500927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240881897496816199973/50000000000000000000)
  centralHi := (481763794993632399947/100000000000000000000)
  directionLo := (96869399479688917681/20000000000000000000)
  directionHi := (242173498699222294203/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree095.table
  base := (53525956239400581338186906400777275034093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-794462886991435283815313206371000000000000)
      constant := (18555272523799610809603097966551214225306837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree095.table
  base := (53525938319570164514054026086020776764377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-832894718070839612544765603877314750000000000)
      constant := (19504571729059430068501522129147557603810398193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96869399479688917681/20000000000000000000)
  centralHi := (242173498699222294203/50000000000000000000)
  directionLo := (486916495521676808093/100000000000000000000)
  directionHi := (243458247760838404047/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree096.table
  base := (55327469890947225263143743147678467584159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-89203301000872953921763675034000000000000)
      constant := (2106018981235743809100251615991678467584159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree096.table
  base := (1106549071387509720903177626938290777279/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-420833134972509516425827509612953000000000000)
      constant := (9961921508101809895038879403777394948085452775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486916495521676808093/100000000000000000000)
  centralHi := (243458247760838404047/50000000000000000000)
  directionLo := (489472505186280441123/100000000000000000000)
  directionHi := (122368126296570110281/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree097.table
  base := (14288700793872756142007722155062205472327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-202799132756069471694108236060250000000000)
      constant := (4839327654339238506561726375923677036750943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree097.table
  base := (57154788308998279660768243383213151096859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-90385569329280311739668873905250000000000)
      constant := (2162564783582513436629093845982140885471859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489472505186280441123/100000000000000000000)
  centralHi := (122368126296570110281/25000000000000000000)
  directionLo := (492015236609147659793/100000000000000000000)
  directionHi := (246007618304573829897/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree098.table
  base := (59007955490503772901403287357758903378077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-819563353040699188256992813176000000000000)
      constant := (19764691877082636185474015346713455130402693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree098.table
  base := (236031767795441690886160519943743739593/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-429604686846688936732716924961544250000000000)
      constant := (10387879410542418459042054493208389742447567125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492015236609147659793/100000000000000000000)
  centralHi := (246007618304573829897/50000000000000000000)
  directionLo := (24727244730144206757/5000000000000000000)
  directionHi := (494544894602884135141/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree099.table
  base := (12177385258912710319232782677488535204469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-91992241673013387748616964679000000000000)
      constant := (2241812733936215943508857871025161426022345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree099.table
  base := (60886913959299050011549238554400846748249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-867980925567557293772323265271679750000000000)
      constant := (21208403328290925869784012604097420229163649841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24727244730144206757/5000000000000000000)
  centralHi := (494544894602884135141/100000000000000000000)
  directionLo := (248530839384169786777/50000000000000000000)
  directionHi := (99412335753667914711/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree100.table
  base := (62791715101022763565065155802931230753687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-836296997073541791218112551046000000000000)
      constant := (20592178798007047570778793483076381076783183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree100.table
  base := (31395851932173477895219677911600212388941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-438376238720868357039606340310135500000000000)
      constant := (10822752782933880170765921619636833507742545869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248530839384169786777/50000000000000000000)
  centralHi := (99412335753667914711/20000000000000000000)
  directionLo := (499565783678408285583/100000000000000000000)
  directionHi := (31222861479900517849/6250000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree101.table
  base := (40451450920219482539400789806831249939/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-52791488693122693293667026248812500000000)
      constant := (1313267778180511018272852595002724296820100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree101.table
  base := (64722311236177028195719826028046658286909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-885524029315916134386102095968862250000000000)
      constant := (22087065529789915037813426311859333951180901781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499565783678408285583/100000000000000000000)
  centralHi := (31222861479900517849/6250000000000000000)
  directionLo := (251028699526789388797/50000000000000000000)
  directionHi := (100411479810715755519/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree102.table
  base := (66678745015079462109981107667457510278411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-94781182345153821575470254324000000000000)
      constant := (2381847951169789535724362753963582510278411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree102.table
  base := (66678735690137349770007324754091050819467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-894295581190095554692991511317453500000000000)
      constant := (22533083216438200067272242122435111533097865003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251028699526789388797/50000000000000000000)
  centralHi := (100411479810715755519/20000000000000000000)
  directionLo := (20181468397187224163/4000000000000000000)
  directionHi := (126134177482420151019/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree103.table
  base := (429131158595483673850557409684330456487/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-53837341445175355978737009865687500000000)
      constant := (1366576257733841496576968985019697162958830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree103.table
  base := (2145655527509750782373821971711726705639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-112883391633034371874985115833255593750000000)
      constant := (2872944827819736596170250356917399033353976279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20181468397187224163/4000000000000000000)
  centralHi := (126134177482420151019/25000000000000000000)
  directionLo := (50700389681824822133/10000000000000000000)
  directionHi := (507003896818248221331/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree104.table
  base := (69012736557136809609013606396046172729/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 5625000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (545662305418780531340861017500000000000)
      linear := (-54360267821201687321272001674125000000000)
      constant := (1393628133603894934889171147780310095491904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree104.table
  base := (2826761379822008596505564558074770466971/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-911838684938454395306770342014636000000000000)
      constant := (23438491745221374899170090917024330008093253475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50700389681824822133/10000000000000000000)
  centralHi := (507003896818248221331/100000000000000000000)
  directionLo := (254729567929947578313/50000000000000000000)
  directionHi := (509459135859895156627/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree105.table
  base := (72702915306206822687502203368964895364077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-97570123017294255402323543969000000000000)
      constant := (2526124622190176451629673142188183645364077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree105.table
  base := (18175727063978098464798528544931983394417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-230152559203158453903414939340806812500000000)
      constant := (5974470645448673865220677117283287412129163303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254729567929947578313/50000000000000000000)
  centralHi := (509459135859895156627/100000000000000000000)
  directionLo := (255951299485533640713/50000000000000000000)
  directionHi := (511902598971067281427/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree106.table
  base := (18690651083109522037391662105998568042943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-221624482293017400025367941164000000000000)
      constant := (5794108626891962966765302342621893362386487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree106.table
  base := (74762597909488608260122518768250264056871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-929381788686813235920549172711818500000000000)
      constant := (24361731129907633700931570989505610820448599239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255951299485533640713/50000000000000000000)
  centralHi := (511902598971067281427/100000000000000000000)
  directionLo := (128583613496130299963/25000000000000000000)
  directionHi := (514334453984521199853/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree107.table
  base := (19212027270247627316313785441999105166489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (216)
      previous := (108)
      next := (108)
      square := (2182649221675122125363444070000000000000)
      linear := (-223716187797122725395507908397750000000000)
      constant := (5905497214785301985991019624936734133998401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree107.table
  base := (76848103229548599011265337294446686113643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-938153340560992656227438588060409750000000000)
      constant := (24830037387426884611405646537251804688002641987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128583613496130299963/25000000000000000000)
  centralHi := (514334453984521199853/100000000000000000000)
  directionLo := (129188716195963148487/25000000000000000000)
  directionHi := (516754864783852593949/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree108.table
  base := (39479714671386555488486536264175887827587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-50179531844717344614588416807000000000000)
      constant := (1337321369586102084436517453867675887827587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree108.table
  base := (19739856002997035158004346000985894966321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-236731223108793019133582000852250250000000000)
      constant := (6325700338108007883689480229902207465425614289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129188716195963148487/25000000000000000000)
  centralHi := (516754864783852593949/100000000000000000000)
  directionLo := (259581995716189839143/50000000000000000000)
  directionHi := (519163991432379678287/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree109.table
  base := (40548282464740439432142396863872787404321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-455799197610666752271575685730500000000000)
      constant := (12262910943049497732478497778652714461638889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree109.table
  base := (81096560073039916049699981733207298280503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-955696444309351496841217418757592250000000000)
      constant := (25780023023194007784651560463144998256630627727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259581995716189839143/50000000000000000000)
  centralHi := (519163991432379678287/100000000000000000000)
  directionLo := (260780995148334295859/50000000000000000000)
  directionHi := (521561990296668591719/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree110.table
  base := (41629757835750469113104514463352469635669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-459982608618877403011855620198000000000000)
      constant := (12492050279131082953477145587426734726721021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree110.table
  base := (41629755623610376913790760738630545976991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-482233998091765458574053417053091750000000000)
      constant := (13130851199077891100519178729366241818816258319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260780995148334295859/50000000000000000000)
  centralHi := (521561990296668591719/100000000000000000000)
  directionLo := (16373406692655327731/3125000000000000000)
  directionHi := (523949014164970487393/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree111.table
  base := (17089656283206774472913815296114621595141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-103148004361575123056030123259000000000000)
      constant := (2827402296407128232840623411940041857975705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree111.table
  base := (5340517336593134900495489606109155561237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-121654943507213792181874531181846843750000000)
      constant := (3343479934489379095151948888148108892818154741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16373406692655327731/3125000000000000000)
  centralHi := (523949014164970487393/100000000000000000000)
  directionLo := (263162606180412088323/50000000000000000000)
  directionHi := (526325212360824176647/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree112.table
  base := (10957857753175935784486781009673375262851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-117087357658824676123103872283250000000000)
      constant := (3239172776633238784469964745039810377365659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree112.table
  base := (43831429176798906171898210406269994642833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-491005549965944878880942832401683000000000000)
      constant := (13619217127604299114162489721375980379594415697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263162606180412088323/50000000000000000000)
  centralHi := (526325212360824176647/100000000000000000000)
  directionLo := (264345365426031674587/50000000000000000000)
  directionHi := (21147629234082533967/4000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree113.table
  base := (44951628687781397513747127984131515537169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-472532841643509355232695423600500000000000)
      constant := (13192192596675451791571200171843918014834521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree113.table
  base := (11237906753825020610675792732211084672373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5880625000000000000000000000000000000000000
      center := (56454)
      previous := (28227)
      next := (28227)
      square := (570459625742811779931795701517500000000000)
      linear := (-61923915737879323629298442509497328125000000)
      constant := (1733342920931157545835114599868994969105827216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264345365426031674587/50000000000000000000)
  centralHi := (21147629234082533967/4000000000000000000)
  directionLo := (106209142471090709981/20000000000000000000)
  directionHi := (265522856177726774953/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree114.table
  base := (46084733677347104648092030762012105338153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-52968472516857778441441706452000000000000)
      constant := (1492201644861826872989166250550324605338153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree114.table
  base := (1843389286150567615917684731652138226819/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-499777101840124299187832247750274250000000000)
      constant := (14116498456979756252791206062021493538622249275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106209142471090709981/20000000000000000000)
  centralHi := (265522856177726774953/50000000000000000000)
  directionLo := (266695148218585583877/50000000000000000000)
  directionHi := (106678059287434233551/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree115.table
  base := (94461491862027836867207061048125960006927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-961799327319861313426510585071000000000000)
      constant := (27339115454644885637814685025703602390062343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree115.table
  base := (1180768613577397993004826299415549535479/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-126040719444303502335319238856142468750000000)
      constant := (3592120598933462249429183476929972521369390985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266695148218585583877/50000000000000000000)
  centralHi := (106678059287434233551/20000000000000000000)
  directionLo := (133931154902331153691/25000000000000000000)
  directionHi := (107144923921864922953/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree116.table
  base := (96779330806723547261317036403459751887373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-970166149336282614907070454006000000000000)
      constant := (27822842733929348180858261927847137766986357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree116.table
  base := (24194832069525768892158464267853905075989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (225816)
      previous := (112908)
      next := (112908)
      square := (2281838502971247119727182806070000000000000)
      linear := (-254274326857151859747360831549432750000000000)
      constant := (7311347591647624660593783538117320885047480501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133931154902331153691/25000000000000000000)
  centralHi := (107144923921864922953/20000000000000000000)
  directionLo := (107609763084541316683/20000000000000000000)
  directionHi := (67256101927838322927/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree117.table
  base := (49561492053443991241795140622400008720089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (48)
      previous := (24)
      next := (24)
      square := (485033160372249361191876460000000000000)
      linear := (-54362942852927995354868351274500000000000)
      constant := (1572822858034957284498967214401634383720089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree117.table
  base := (99122981803511564853032913515157890128363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1025868859302786859296332741546322250000000000)
      constant := (29758273638577541763009073709123237969077142467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107609763084541316683/20000000000000000000)
  centralHi := (67256101927838322927/12500000000000000000)
  directionLo := (540363014555955707667/100000000000000000000)
  directionHi := (135090753638988926917/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree118.table
  base := (101492451688687062488354576527767398394443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-986899793369125217868190191876000000000000)
      constant := (28803021586080027737773078848451031585549987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree118.table
  base := (12686556198816887645878109441855909805593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (112908)
      previous := (56454)
      next := (56454)
      square := (1140919251485623559863591403035000000000000)
      linear := (-129330051397120784950402769611864187500000000)
      constant := (3784451825844060959986312315121929500478012037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540363014555955707667/100000000000000000000)
  centralHi := (135090753638988926917/25000000000000000000)
  directionLo := (542667344901296066757/100000000000000000000)
  directionHi := (271333672450648033379/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree119.table
  base := (103887733485547748955670897719955035938463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-995266615385546519348750060811000000000000)
      constant := (29299473157682580686353817674720314073446167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree119.table
  base := (103887731574378708144890002562221776403317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1043411963051145699910111572243504750000000000)
      constant := (30797413270505680460394351549019100403163184653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542667344901296066757/100000000000000000000)
  centralHi := (271333672450648033379/50000000000000000000)
  directionLo := (108992386329402742267/20000000000000000000)
  directionHi := (68120241455876713917/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree120.table
  base := (106308829437439912644329361949992396847797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-111514826377996424536589992194000000000000)
      constant := (3311129573210735422616970821354992396847797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree120.table
  base := (106308827696632091782238997871277839854181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1052183514925325120217000987592096000000000000)
      constant := (31323669629287537648233333900359263820187989029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108992386329402742267/20000000000000000000)
  centralHi := (68120241455876713917/12500000000000000000)
  directionLo := (136811724339205178613/25000000000000000000)
  directionHi := (547246897356820714453/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree121.table
  base := (21751147898046022626013867946036713023429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-1012000259418389122309869798681000000000000)
      constant := (30305100589234941125551492335485620836054305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree121.table
  base := (54377868952318794353893987674525498861763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-530477533399752270261945201470343625000000000)
      constant := (15927191841301301644373517745279521773282515567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136811724339205178613/25000000000000000000)
  centralHi := (547246897356820714453/100000000000000000000)
  directionLo := (549522362046249114141/100000000000000000000)
  directionHi := (274761181023124557071/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree122.table
  base := (55614231797549979277602971826125825433739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-510183540717405211895214833808000000000000)
      constant := (15407138224129091062815459258958944928903651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree122.table
  base := (22245692430184281898238196737632877720339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1069726618673683960830779818289278500000000000)
      constant := (32389555430004196497185331263767330693290848255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549522362046249114141/100000000000000000000)
  centralHi := (274761181023124557071/50000000000000000000)
  directionLo := (3448677770351309261/625000000000000000)
  directionHi := (551788443256209481761/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree123.table
  base := (113727001708022478923567728035438293964153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (96)
      previous := (48)
      next := (48)
      square := (970066320744498722383752920000000000000)
      linear := (-114303767050136858363443281839000000000000)
      constant := (3480854859507788785980608103151657043964153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree123.table
  base := (11372700039268172959637324235473676394217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-539249085273931690568834616818934875000000000)
      constant := (16464592435544797453244146804970418296395626265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3448677770351309261/625000000000000000)
  centralHi := (551788443256209481761/100000000000000000000)
  directionLo := (34627828507740105379/6250000000000000000)
  directionHi := (110809051224768337213/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree124.table
  base := (116251353789290629900836471303923780097177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-1037100725467653026751549405486000000000000)
      constant := (31845352450813328571126291572644314020874593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree124.table
  base := (116251352591327852623034018118318842161761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1087269722422042801444558648986461000000000000)
      constant := (33473272005495698654225492930114263954650009249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34627828507740105379/6250000000000000000)
  centralHi := (110809051224768337213/20000000000000000000)
  directionLo := (556292913450778694669/100000000000000000000)
  directionHi := (55629291345077869467/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree125.table
  base := (59400759901546327117380258807961720173877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (432)
      previous := (216)
      next := (216)
      square := (4365298443350244250726888140000000000000)
      linear := (-522733773742037164116054637210500000000000)
      constant := (16183626296832782401131554774090014856564893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree125.table
  base := (118801518712065270376937867939430806364549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1096041274296222221751448064335052250000000000)
      constant := (34021816832895126212797367940729147181693416541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556292913450778694669/100000000000000000000)
  centralHi := (55629291345077869467/10000000000000000000)
  directionLo := (279265762884468966271/50000000000000000000)
  directionHi := (558531525768937932543/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree126.table
  base := (3034437492928239323295122137854152973101/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (12)
      previous := (6)
      next := (6)
      square := (121258290093062340297969115000000000000)
      linear := (-14636588465284661523787071435500000000000)
      constant := (456852696719946068837418222525786389865505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree126.table
  base := (60688749361760990046463873008481577710763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-552406413085200821029168739841821750000000000)
      constant := (17287409676496349204093277998921423488899319067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279265762884468966271/50000000000000000000)
  centralHi := (558531525768937932543/100000000000000000000)
  directionLo := (112152240280789754717/20000000000000000000)
  directionHi := (280380600701974386793/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree127.table
  base := (123979293502270565415437895156028700386579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (864)
      previous := (432)
      next := (432)
      square := (8730596886700488501453776280000000000000)
      linear := (-1062201191516916931193229012291000000000000)
      constant := (33423777161062807648030513875090477053479211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree127.table
  base := (123979292597411897896247578088760332188563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (903264)
      previous := (451632)
      next := (451632)
      square := (9127354011884988478908731224280000000000000)
      linear := (-1113584378044581062365226895032234750000000000)
      constant := (35132279565522271477215477198722741705796564267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112152240280789754717/20000000000000000000)
  centralHi := (280380600701974386793/50000000000000000000)
  directionLo := (11259640930726383021/2000000000000000000)
  directionHi := (562982046536319151051/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree128.table
  base := (15825862641530304177228333488811630945013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (1091324610837561062681722035000000000000)
      linear := (-133821001691667279084223610153250000000000)
      constant := (4244800198138647261632727400025304678505117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree128.table
  base := (12660690030823163560482536453798702406913/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-561177964959380241336058155190413000000000000)
      constant := (17847098735121942020239508049487013954733222085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell042.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11259640930726383021/2000000000000000000)
  centralHi := (562982046536319151051/100000000000000000000)
  directionLo := (141298541315109752897/25000000000000000000)
  directionHi := (565194165260439011589/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree129.table
  base := (32315080645837433241060317480353802612591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (24)
      previous := (12)
      next := (12)
      square := (242516580186124680595938230000000000000)
      linear := (-29970412098604431504287465282250000000000)
      constant := (958257428771165813767096072013533490112591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree129.table
  base := (64630160916493645403284832820606941514599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (451632)
      previous := (225816)
      next := (225816)
      square := (4563677005942494239454365612140000000000000)
      linear := (-565563740896469951489502862864708625000000000)
      constant := (18130286533470593235090902171119479426578049491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell042.Kernel129
