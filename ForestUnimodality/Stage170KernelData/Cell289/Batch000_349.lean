import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell289.Parameters
import ForestUnimodality.BinomialMassData.Q3_5.Batch000_049
import ForestUnimodality.BinomialMassData.Q3_5.Batch050_099
import ForestUnimodality.BinomialMassData.Q123_203.Batch000_049
import ForestUnimodality.BinomialMassData.Q123_203.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree000.table
  base := (1750319064787449023889109887/100000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-927390963514526135702542575000000000000)
      constant := (218789883098431127986138735875000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree000.table
  base := (1750319064787449023889109887/100000000000000000000000000)
  polynomial :=
    { denominator := 507500000000000000000000000000000000000000
      center := (1353)
      previous := (0)
      next := (880)
      square := (11483748085004829107141910655000000000000)
      linear := (-37652073118689761109523228545000000000000)
      constant := (8882869253796303796237232676525000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree001.table
  base := (143370862334208956844488934250757567521657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-5067248356718773993900839540000000000000)
      constant := (719487355334277847783457974205787837608285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree001.table
  base := (143061742393353913842462778512826533038899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-41873491488020837862360501663060000000000000)
      constant := (5917379563735575676020859190667868599999988891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48865405980836431213/100000000000000000000)
  directionHi := (24432702990418215607/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree002.table
  base := (58676966011518611002051086491012769055303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-3212466429689721722495754390000000000000)
      constant := (296425179071624319406595936179063845276515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree002.table
  base := (116847523513033512148172033315984430585551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-53173499603665589703788141747580000000000000)
      constant := (4865912842291224239129492667761322399999971159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48865405980836431213/100000000000000000000)
  centralHi := (24432702990418215607/50000000000000000000)
  directionLo := (34553059934483117077/50000000000000000000)
  directionHi := (13821223973793246831/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree003.table
  base := (95982790792359321964428561940192233570249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-7782617362040112896082178020000000000000)
      constant := (490256917056285005517145923188961167851245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree003.table
  base := (95360581630278064906664223105113672191373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-64473507719310341545215781832100000000000000)
      constant := (4016099281586444766324708357668989317334289957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34553059934483117077/50000000000000000000)
  centralHi := (13821223973793246831/20000000000000000000)
  directionLo := (84637365891288787119/100000000000000000000)
  directionHi := (1057967073641109839/1250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree004.table
  base := (78420895008223381977319782414741687663277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-9140301864700782347172847260000000000000)
      constant := (407524313903627574154578533145708438316385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree004.table
  base := (19435337019220602197122172647774590086963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-18943378958738773346660855479155000000000000)
      constant := (833129229093292670490793531040923082893658267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84637365891288787119/100000000000000000000)
  centralHi := (1057967073641109839/1250000000000000000)
  directionLo := (48865405980836431213/50000000000000000000)
  directionHi := (97730811961672862427/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree005.table
  base := (31987652954744141074949144999170023428889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-5248993183680725899131758250000000000000)
      constant := (170593927439785372630550990095850117144445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree005.table
  base := (31639761340968370952052471553713238416347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-43536761975299922614035531000570000000000000)
      constant := (1392947493454189979989407902475568841899243523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48865405980836431213/50000000000000000000)
  centralHi := (97730811961672862427/100000000000000000000)
  directionLo := (109266369521275045931/100000000000000000000)
  directionHi := (27316592380318761483/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree006.table
  base := (1627711866180810699670720613631143414761/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-2963917717505530312338546435000000000000)
      constant := (72112830273068529593302784763245736590440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree006.table
  base := (6425358536760165832010552975781748301577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-24593383016561149267374675521415000000000000)
      constant := (588163043105422293429800000222130131519373186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109266369521275045931/100000000000000000000)
  centralHi := (27316592380318761483/25000000000000000000)
  directionLo := (119695310726994602561/100000000000000000000)
  directionHi := (59847655363497301281/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree007.table
  base := (8459218940312917899928149532857409975279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-13213355372682790700444854980000000000000)
      constant := (247018603883978827509039291409435249381975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree007.table
  base := (520531570721020907924397664869505491529/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14717500000000000000000000000000000000000000
      center := (39237)
      previous := (0)
      next := (25520)
      square := (333028694465140044107115408995000000000000)
      linear := (-3916912149353191032533083648935000000000000)
      constant := (71909544708844878852108902527925576572624460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695310726994602561/100000000000000000000)
  centralHi := (59847655363497301281/50000000000000000000)
  directionLo := (129285711939501474187/100000000000000000000)
  directionHi := (32321427984875368547/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree008.table
  base := (684530479360387191838644597975541938471/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-7285519937671730075767762110000000000000)
      constant := (107503034395330276613045408170942742308875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree008.table
  base := (16807348640407988267060018664646579961377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-60486774148767050376176991127350000000000000)
      constant := (876262157170838335030421942565100913628384793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129285711939501474187/100000000000000000000)
  centralHi := (32321427984875368547/25000000000000000000)
  directionLo := (138212239737932468309/100000000000000000000)
  directionHi := (13821223973793246831/10000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree009.table
  base := (27569094119541640840852704642438032345439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-15928724378004129602626193460000000000000)
      constant := (190868848824276236396941705364190161727195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree009.table
  base := (27005292778746487999643549432680080235593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-132273556413178852593781622339220000000000000)
      constant := (1556880009239091405865214806150033426428551937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138212239737932468309/100000000000000000000)
  centralHi := (13821223973793246831/10000000000000000000)
  directionLo := (3664905448562732341/2500000000000000000)
  directionHi := (146596217942509293641/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree010.table
  base := (22070422883443477625626339152875496305603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-17286408880664799053716862700000000000000)
      constant := (173340032621386098917712794764377481528015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree010.table
  base := (2155729108322495127275747016662794277719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-71786782264411802217604631211870000000000000)
      constant := (707971377669229221875214560701985446952611355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3664905448562732341/2500000000000000000)
  centralHi := (146596217942509293641/100000000000000000000)
  directionLo := (154525981688257358957/100000000000000000000)
  directionHi := (77262990844128679479/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree011.table
  base := (17522725259380954108028961852899096201963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-18644093383325468504807531940000000000000)
      constant := (161380695180270561597283226656495481009815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree011.table
  base := (8530189621656753614034920058993799805061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-77436786322234178138318451254130000000000000)
      constant := (660522883122289773509104787717775496166758749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154525981688257358957/100000000000000000000)
  centralHi := (77262990844128679479/50000000000000000000)
  directionLo := (16206821686682313061/10000000000000000000)
  directionHi := (162068216866823130611/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree012.table
  base := (6877805740727735971262409553908151178827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-10000888942993068977949100590000000000000)
      constant := (77069443835718316353987116433540755894135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree012.table
  base := (13342467571849430523383145065957789939399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-166173580760113108118064542592780000000000000)
      constant := (1265097398039165967041938804719774565612693391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16206821686682313061/10000000000000000000)
  centralHi := (162068216866823130611/100000000000000000000)
  directionLo := (169274731782577574239/100000000000000000000)
  directionHi := (1057967073641109839/625000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree013.table
  base := (265733963465225002383198584046089848039/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-5339865597161701851747217605000000000000)
      constant := (37728998759898539270213993904304492401950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree013.table
  base := (1026274431940620830022664867799112480327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-88736794437878929979746091338650000000000000)
      constant := (621147469670050267718448117864348131008976715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169274731782577574239/100000000000000000000)
  centralHi := (1057967073641109839/625000000000000000)
  directionLo := (176186726860270445307/100000000000000000000)
  directionHi := (44046681715067611327/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree014.table
  base := (8029391570377610473351333445449678702327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-22717146891307476858079539660000000000000)
      constant := (151139142982423494250493449059248393511635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree014.table
  base := (7705991580417421379711174469032121945739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (156948)
      previous := (0)
      next := (102080)
      square := (1332114777860560176428461635980000000000000)
      linear := (-26967656713057515971559974680260000000000000)
      constant := (178270053639556669180033970669952101894565493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176186726860270445307/100000000000000000000)
  centralHi := (44046681715067611327/25000000000000000000)
  directionLo := (182837607245904167319/100000000000000000000)
  directionHi := (4570940181147604183/2500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree015.table
  base := (5861757999341008083315778630845066554327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-24074831393968146309170208900000000000000)
      constant := (154338568612823169250490599554225332771635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree015.table
  base := (22311735233279267074059474510230538609/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-100036802553523681821173731423170000000000000)
      constant := (638999352725614660455081603941811283192285125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182837607245904167319/100000000000000000000)
  centralHi := (4570940181147604183/2500000000000000000)
  directionLo := (189254903569443803541/100000000000000000000)
  directionHi := (94627451784721901771/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree016.table
  base := (4049415996031797710413081133292374695297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-25432515896628815760260878140000000000000)
      constant := (160129062783456206006806438178461873476485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree016.table
  base := (3801431525423671066480993952074422537691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-211373613222692115483775102930860000000000000)
      constant := (1329441088526982633789613491974234878355708419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189254903569443803541/100000000000000000000)
  centralHi := (94627451784721901771/50000000000000000000)
  directionLo := (195461623923345724853/100000000000000000000)
  directionHi := (97730811961672862427/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree017.table
  base := (632297709393398837639857080519776287841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-6697550099822371302837886845000000000000)
      constant := (42048687969985171124755475444598881439205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree017.table
  base := (115668336686568856875867630705411570473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-55668405334584216831300685753845000000000000)
      constant := (349904123781168307606841316661976527038109285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195461623923345724853/100000000000000000000)
  centralHi := (97730811961672862427/50000000000000000000)
  directionLo := (100738615148838782633/50000000000000000000)
  directionHi := (201477230297677565267/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree018.table
  base := (1249279013223819533594877606121857786313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-28147884901950154662442216620000000000000)
      constant := (178276618348563697376337277398609288931565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree018.table
  base := (1062094367371602667720815738207836841301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-233973629453981619166630383099900000000000000)
      constant := (1486396683724809377499784494076166748393172909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100738615148838782633/50000000000000000000)
  centralHi := (201477230297677565267/100000000000000000000)
  directionLo := (1619674684428896113/781250000000000000)
  directionHi := (41463671921379740493/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree019.table
  base := (41800380916440772677266846237743454373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-7376392351152706028383221465000000000000)
      constant := (47540566798185427198675189259188717271865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree019.table
  base := (1071387262122632070561044264640221549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-245273637569626371008058023184420000000000000)
      constant := (1588040265420590910130771109210427794449063705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1619674684428896113/781250000000000000)
  centralHi := (41463671921379740493/20000000000000000000)
  directionLo := (42599873301110806181/20000000000000000000)
  directionHi := (106499683252777015453/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree020.table
  base := (-751874456566613233921180035004420183271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-30863253907271493564623555100000000000000)
      constant := (203677534285144522474996452224977899083645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree020.table
  base := (-222855452610206287881156548901876734981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-64143411421317780712371415817235000000000000)
      constant := (425780596871250623504644810863002561628167971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42599873301110806181/20000000000000000000)
  centralHi := (106499683252777015453/50000000000000000000)
  directionLo := (218532739042550091863/100000000000000000000)
  directionHi := (27316592380318761483/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree021.table
  base := (-768255921998686890704186329957541484257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-16110469204966081507857112170000000000000)
      constant := (109339802521575908355830911466212292578715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree021.table
  base := (-25883329421869509092496773854871803863/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14717500000000000000000000000000000000000000
      center := (39237)
      previous := (0)
      next := (25520)
      square := (333028694465140044107115408995000000000000)
      linear := (-9566916207175566953246903691195000000000000)
      constant := (65374185622869117878544294406561915050536304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218532739042550091863/100000000000000000000)
  centralHi := (27316592380318761483/12500000000000000000)
  directionLo := (223929421771930769443/100000000000000000000)
  directionHi := (55982355442982692361/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree022.table
  base := (-2210132202043021219658131612558783365711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-33578622912592832466804893580000000000000)
      constant := (235051371649681078165168763545206083171445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree022.table
  base := (-115656273784471527991934548483962094269/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-69793415479140156633085235859495000000000000)
      constant := (492287691215777298109211523528252030286343895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223929421771930769443/100000000000000000000)
  centralHi := (55982355442982692361/25000000000000000000)
  directionLo := (45839814064537053689/20000000000000000000)
  directionHi := (114599535161342634223/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree023.table
  base := (-279194116918716202807517130882005175579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-17468153707626750958947781410000000000000)
      constant := (126348402956157137219246850991949870610525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree023.table
  base := (-360017467755083712740424908001849974569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-72618417508051344593442145880625000000000000)
      constant := (529590640060271463009548322611393528795972158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45839814064537053689/20000000000000000000)
  centralHi := (114599535161342634223/50000000000000000000)
  directionLo := (117175127201184629039/50000000000000000000)
  directionHi := (234350254402369258079/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree024.table
  base := (-1648843659154225862272642492327779429453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-18146995958957085684493116030000000000000)
      constant := (135768582483329063971103836034361102852735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree024.table
  base := (-674614732165113268124519207001106566993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-301773678147850130215196223607020000000000000)
      constant := (2277473935608841675903404276120976997403927315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117175127201184629039/50000000000000000000)
  centralHi := (234350254402369258079/100000000000000000000)
  directionLo := (119695310726994602561/50000000000000000000)
  directionHi := (239390621453989205123/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree025.table
  base := (-3740284426720960201333591986121361481303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-37651676420574840820076901300000000000000)
      constant := (291507879926142289214985077069393192593485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree025.table
  base := (-951151968807947174137824374548754499427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-78268421565873720514155965922885000000000000)
      constant := (611490583585314011082288711978220375833112757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695310726994602561/50000000000000000000)
  centralHi := (239390621453989205123/100000000000000000000)
  directionLo := (244327029904182156067/100000000000000000000)
  directionHi := (61081757476045539017/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree026.table
  base := (-516290217631723382979022885585858199641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-9752340230808877567791892635000000000000)
      constant := (78139001139405315057466365782141418003590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree026.table
  base := (-2092558987308285353173821161593304856713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-162186847189569816949025751888030000000000000)
      constant := (1311700094388253352010261974692801500159713983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244327029904182156067/100000000000000000000)
  centralHi := (61081757476045539017/25000000000000000000)
  directionLo := (249165658635918538197/100000000000000000000)
  directionHi := (124582829317959269099/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree027.table
  base := (-895296479311782355882426442537148457451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-40367045425896179722258239780000000000000)
      constant := (334638123184835143649993460584571288563725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree027.table
  base := (-452309349557155939246286717918829764917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-167836851247392192869739571930290000000000000)
      constant := (1404718826800594236414659284318874721087676735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249165658635918538197/100000000000000000000)
  centralHi := (124582829317959269099/50000000000000000000)
  directionLo := (253912097673866361359/100000000000000000000)
  directionHi := (3173901220923329517/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree028.table
  base := (-1196471630532233347456501441371833533117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-10431182482139212293337227255000000000000)
      constant := (89429658790830236066651559365140832334415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree028.table
  base := (-4825480760966016308635177397299884196657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (156948)
      previous := (0)
      next := (102080)
      square := (1332114777860560176428461635980000000000000)
      linear := (-49567672944347019654415254849300000000000000)
      constant := (429112639685168850198220143168575581734280241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253912097673866361359/100000000000000000000)
  centralHi := (3173901220923329517/1250000000000000000)
  directionLo := (129285711939501474187/50000000000000000000)
  directionHi := (2068571391032023587/800000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree029.table
  base := (-633046573371088318608009948760976654637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-10770603607804379656109894565000000000000)
      constant := (95442087036763597202688103630390233453630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree029.table
  base := (-318622712535279277926677977449454030503/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3552500000000000000000000000000000000000000
      center := (9471)
      previous := (0)
      next := (6160)
      square := (80386236595033803749993374585000000000000)
      linear := (-3088566540742016288123572620945000000000000)
      constant := (27639814178125178852443257529997303290620948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129285711939501474187/50000000000000000000)
  centralHi := (2068571391032023587/800000000000000000)
  directionLo := (263148264574340259887/100000000000000000000)
  directionHi := (16446766535896266243/6250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree030.table
  base := (-5316728105001499135226560527625420033659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-44440098933878188075530247500000000000000)
      constant := (406763324566419137888930957561872899831705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree030.table
  base := (-2672595940311878161403554519511505101001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-184786863420859320631881032057070000000000000)
      constant := (1708267956568113359251307468364550386292849791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263148264574340259887/100000000000000000000)
  centralHi := (16446766535896266243/6250000000000000000)
  directionLo := (16727928210844981453/6250000000000000000)
  directionHi := (267646851373519703249/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree031.table
  base := (-1386719703085441778131272082152116458169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-11449445859134714381655229185000000000000)
      constant := (108170983935210727920770916957239417709155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree031.table
  base := (-557097131099973700550766113218676297111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-190436867478681696552594852099330000000000000)
      constant := (1817292039222624926145762892887157842361764005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16727928210844981453/6250000000000000000)
  centralHi := (267646851373519703249/100000000000000000000)
  directionLo := (272071065995322094859/100000000000000000000)
  directionHi := (13603553299766104743/5000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree032.table
  base := (-287902189625496377124831483181755482871/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-11788866984799881744427896495000000000000)
      constant := (114878521563180906221131427992456112928225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree032.table
  base := (-5778415113625158055538198842002715175889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-392173743073008144946617344283180000000000000)
      constant := (3860234639585163554024985502520230110316790199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272071065995322094859/100000000000000000000)
  centralHi := (13603553299766104743/5000000000000000000)
  directionLo := (276424479475864936619/100000000000000000000)
  directionHi := (13821223973793246831/5000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree033.table
  base := (-1488215669673828686044665389838813943711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-12128288110465049107200563805000000000000)
      constant := (121810144484028651474517426212805930281445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree033.table
  base := (-5970070757748852892223449071497914220031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-403473751188652896788044984367700000000000000)
      constant := (4093382617895692647326041416020002452906742521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276424479475864936619/100000000000000000000)
  centralHi := (13821223973793246831/5000000000000000000)
  directionLo := (280710385905428943477/100000000000000000000)
  directionHi := (140355192952714471739/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree034.table
  base := (-3066749979574349221813685454135203529419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-24935418472260432939946462230000000000000)
      constant := (257926294174881003046717356005323982352905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree034.table
  base := (-307401131970121626658335720242618354347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-103693439826074412157368156113055000000000000)
      constant := (1083485529375192618442569757520539701178572385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280710385905428943477/100000000000000000000)
  centralHi := (140355192952714471739/50000000000000000000)
  directionLo := (284931831596343066973/100000000000000000000)
  directionHi := (142465915798171533487/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree035.table
  base := (-1575432626781374543567794318820995501317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-12807130361795383832745898425000000000000)
      constant := (136335310781847181950869658905895022493415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree035.table
  base := (-394623516227958108175571709167823463197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14717500000000000000000000000000000000000000
      center := (39237)
      previous := (0)
      next := (25520)
      square := (333028694465140044107115408995000000000000)
      linear := (-15216920264997942873960723733455000000000000)
      constant := (163637244871684158966512531826566093088637044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284931831596343066973/100000000000000000000)
  centralHi := (142465915798171533487/50000000000000000000)
  directionLo := (144545820208090737247/50000000000000000000)
  directionHi := (57818328083236294899/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree036.table
  base := (-3229504857483985504830903015516700088513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-26293102974921102391037131470000000000000)
      constant := (287849632653641742830221424418416499557435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree036.table
  base := (-646932710099132673369544969617490145443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-218686887767793576156163952310630000000000000)
      constant := (2418513664088093690260989191381364242982197065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144545820208090737247/50000000000000000000)
  centralHi := (57818328083236294899/20000000000000000000)
  directionLo := (3664905448562732341/1250000000000000000)
  directionHi := (293192435885018587281/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree037.table
  base := (-1651632750900870615511746194061806588397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-13485972613125718558291233045000000000000)
      constant := (151730171946202363025772178411690967058015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree037.table
  base := (-413451061466273281316681603199710366479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-112168445912807976038438886176445000000000000)
      constant := (1274862119886603482871946856107152542031067556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3664905448562732341/1250000000000000000)
  centralHi := (293192435885018587281/100000000000000000000)
  directionLo := (148618330264021184009/50000000000000000000)
  directionHi := (297236660528042368019/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree038.table
  base := (-3372636489957474500004503005694874489491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-27650787477581771842127800710000000000000)
      constant := (319500308762776022394252383775525627552545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree038.table
  base := (-6752580176220634985485038285740244143937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-459973791766876655995183184790300000000000000)
      constant := (5369067810219767488802670211785290279072500167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148618330264021184009/50000000000000000000)
  centralHi := (297236660528042368019/100000000000000000000)
  directionLo := (301226592889032067871/100000000000000000000)
  directionHi := (9413331027782252121/3125000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree039.table
  base := (-1719009526350541492827206380787552849189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-14164814864456053283836567665000000000000)
      constant := (167983760555503071744471557904062235754055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree039.table
  base := (-137643622539072954326207843482542570251/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-235636899941260703918305412437410000000000000)
      constant := (2822926909035869868627604031734857580563163525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301226592889032067871/100000000000000000000)
  centralHi := (9413331027782252121/3125000000000000000)
  directionLo := (76291090635312157341/25000000000000000000)
  directionHi := (61032872508249725873/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree040.table
  base := (-6999484404139214158368010883132213397213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-58016943960484882586436939900000000000000)
      constant := (705720671753819774759125267984338933013935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree040.table
  base := (-7004645332690611825973500822136141542883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-482573807998166159678038464959340000000000000)
      constant := (5929780726995171909379071124242191743159334453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76291090635312157341/25000000000000000000)
  centralHi := (61032872508249725873/20000000000000000000)
  directionLo := (154525981688257358957/50000000000000000000)
  directionHi := (61810392675302943583/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree041.table
  base := (-7116151462992100693152596072622746771341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-59374628463145552037527609140000000000000)
      constant := (740354808186644472472391706748886266143295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree041.table
  base := (-3560242299421414611862451615421689344091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-246936908056905455759733052521930000000000000)
      constant := (3110413723000434832397976966203687603819353981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154525981688257358957/50000000000000000000)
  centralHi := (61810392675302943583/20000000000000000000)
  directionLo := (312891265407889837029/100000000000000000000)
  directionHi := (31289126540788983703/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree042.table
  base := (-3613240875762929607160540154659007836943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-30366156482903110744309139190000000000000)
      constant := (387917619586330605962196525910704960815285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree042.table
  base := (-7230117706540444509906910495848263599837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (156948)
      previous := (0)
      next := (102080)
      square := (1332114777860560176428461635980000000000000)
      linear := (-72167689175636523337270535018340000000000000)
      constant := (931282388219605839238621455718101272187759581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312891265407889837029/100000000000000000000)
  centralHi := (31289126540788983703/10000000000000000000)
  directionLo := (63336805056845904723/20000000000000000000)
  directionHi := (9896375790132172613/3125000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree043.table
  base := (-293233524163635782465153483181161862627/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-62089997468466890939708947620000000000000)
      constant := (812160150540117968916352435770354767171625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree043.table
  base := (-7333887322960399776303784405975020663787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-516473832345100415202321385212900000000000000)
      constant := (6824214420632590932341922253044535373466001517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63336805056845904723/20000000000000000000)
  centralHi := (9896375790132172613/3125000000000000000)
  directionLo := (64086379136878840853/20000000000000000000)
  directionHi := (160215947842197102133/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree044.table
  base := (-7429518054927565984498714402446327925877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-63447681971127560390799616860000000000000)
      constant := (849328054617812947201155618499768360370615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree044.table
  base := (-7432073837599221687764326421249679246359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-527773840460745167043749025297420000000000000)
      constant := (7136529000716157470478915862094641967936791969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64086379136878840853/20000000000000000000)
  centralHi := (160215947842197102133/50000000000000000000)
  directionLo := (16206821686682313061/5000000000000000000)
  directionHi := (324136433733646261221/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree045.table
  base := (-940345699096768273573130142743573972069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-16201341618447057460472571525000000000000)
      constant := (221834432865513695812632738922564260279310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree045.table
  base := (-470306667706272520847173063125681059627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-134768462144097479721294166345485000000000000)
      constant := (1863977750772473688588189710847315236855323828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16206821686682313061/5000000000000000000)
  centralHi := (324136433733646261221/100000000000000000000)
  directionLo := (163899554281912568897/50000000000000000000)
  directionHi := (65559821712765027559/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree046.table
  base := (-1522156159898618183787824288758175063787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-66163050976448899292980955340000000000000)
      constant := (926188180663531198339221926613045623405325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree046.table
  base := (-951571699908282255233738586642422317127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-137593464173008667681651076366615000000000000)
      constant := (1945588172802252334515217956774854837467026914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163899554281912568897/50000000000000000000)
  centralHi := (65559821712765027559/20000000000000000000)
  directionLo := (331421308121415729309/100000000000000000000)
  directionHi := (33142130812141572931/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree047.table
  base := (-7693727753615059677833742203332437268977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-67520735479109568744071624580000000000000)
      constant := (965878581829588894955864596791337813655115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree047.table
  base := (-1923807052542574081316435221470444465547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-140418466201919855642007986387745000000000000)
      constant := (2028961933588583960713083699539554454019273677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331421308121415729309/100000000000000000000)
  centralHi := (33142130812141572931/10000000000000000000)
  directionLo := (335004345312985975477/100000000000000000000)
  directionHi := (167502172656492987739/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree048.table
  base := (-1554348202227113389343477413202076042819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-68878419981770238195162293820000000000000)
      constant := (1006408262180250300693216547997948098929525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree048.table
  base := (-77729962274769688727891427159258672701/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-143243468230831043602364896408875000000000000)
      constant := (2114097738020533487073803749252692733916612275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335004345312985975477/100000000000000000000)
  centralHi := (167502172656492987739/50000000000000000000)
  directionLo := (338549463565155148479/100000000000000000000)
  directionHi := (1057967073641109839/312500000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree049.table
  base := (-7844930919676389794975832293314589061963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-70236104484430907646252963060000000000000)
      constant := (1047776669977406530204348898925427054690185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree049.table
  base := (-7845980523433829611137851871518082105651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (156948)
      previous := (0)
      next := (102080)
      square := (1332114777860560176428461635980000000000000)
      linear := (-83467697291281275178698175102860000000000000)
      constant := (1257711157875707743517746478751733050644032563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338549463565155148479/100000000000000000000)
  centralHi := (1057967073641109839/312500000000000000)
  directionLo := (171028920932927509247/50000000000000000000)
  directionHi := (68411568373171003699/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree050.table
  base := (-1978346994005352174947997237002012916757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-17898447246772894274335908075000000000000)
      constant := (272495838184284545275836773564989935416215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree050.table
  base := (-63314122261351271967912895540618678503/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-595573889154613678092314865804540000000000000)
      constant := (9158605724333460104791362329815330609696234125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171028920932927509247/50000000000000000000)
  centralHi := (68411568373171003699/20000000000000000000)
  directionLo := (172765299672415585387/50000000000000000000)
  directionHi := (13821223973793246831/4000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree051.table
  base := (-7977186399232766582653250066988643728871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-72951473489752246548434301540000000000000)
      constant := (1133027939364134538782774168817056781355645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree051.table
  base := (-3988959699536880534337501468182717537949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-303436948635129214966871252944530000000000000)
      constant := (4760135485322137299153686123825558392978659659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172765299672415585387/50000000000000000000)
  centralHi := (13821223973793246831/4000000000000000000)
  directionLo := (2791750395550664789/800000000000000000)
  directionHi := (174484399721916549313/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree052.table
  base := (-1004548382569291991546062759354436936691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-18577289498103228999881242695000000000000)
      constant := (294227531375544060199646422618455630633090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree052.table
  base := (-2009249813792670548275319592765056419363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-154543476346475795443792536493395000000000000)
      constant := (2472242880148759093578015727009724790014470133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2791750395550664789/800000000000000000)
  centralHi := (174484399721916549313/50000000000000000000)
  directionLo := (176186726860270445307/50000000000000000000)
  directionHi := (70474690744108178123/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree053.table
  base := (-1011379985736324412315870417459050888531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-18916710623768396362653910005000000000000)
      constant := (305407415380435223600708891847409491114690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree053.table
  base := (-2022887749055492397888092190530957115631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-157368478375386983404149446514525000000000000)
      constant := (2566176368146407856643078803466749788221962121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176186726860270445307/50000000000000000000)
  centralHi := (70474690744108178123/20000000000000000000)
  directionLo := (355745525324794686571/100000000000000000000)
  directionHi := (88936381331198671643/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree054.table
  base := (-8141185825805720479403594578964004454897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-77024526997734254901706309260000000000000)
      constant := (1267186342670007620604148995977179977725515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree054.table
  base := (-1628322478186431033303579241105159496957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-640773921617192685458025426142620000000000000)
      constant := (10647471270205514699918434328182607411449494935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355745525324794686571/100000000000000000000)
  centralHi := (88936381331198671643/25000000000000000000)
  directionLo := (359085932180983807683/100000000000000000000)
  directionHi := (89771483045245951921/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree055.table
  base := (-1023357308862046341537103181005778316283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-19595552875098731088199244625000000000000)
      constant := (328395000248498280779008456989942216837170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree055.table
  base := (-327488574155873209210707673996856233373/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-652073929732837437299453066227140000000000000)
      constant := (11037267639495116471963092779180788786973301075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359085932180983807683/100000000000000000000)
  centralHi := (89771483045245951921/25000000000000000000)
  directionLo := (181197774953197250493/50000000000000000000)
  directionHi := (362395549906394500987/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree056.table
  base := (-8228085376376925546277023265168855919427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-79739896003055593803887647740000000000000)
      constant := (1360810498717625504493138226746155720402865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree056.table
  base := (-8228382191289645513719630262541468210569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (156948)
      previous := (0)
      next := (102080)
      square := (1332114777860560176428461635980000000000000)
      linear := (-94767705406926027020125815187380000000000000)
      constant := (1633441933944618109962270839117218376644380297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181197774953197250493/50000000000000000000)
  centralHi := (362395549906394500987/100000000000000000000)
  directionLo := (365675214491808334639/100000000000000000000)
  directionHi := (4570940181147604183/1250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree057.table
  base := (-8264889148223998790676481870504753996923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-81097580505716263254978316980000000000000)
      constant := (1408877722811021695388800723135476230015385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree057.table
  base := (-258285519378143060704650747704818016217/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-168668486491031735245577086599045000000000000)
      constant := (2959487027707676408526674475445737234957709176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365675214491808334639/100000000000000000000)
  centralHi := (4570940181147604183/1250000000000000000)
  directionLo := (720558056186726821/195312500000000000)
  directionHi := (368925724767604132353/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree058.table
  base := (-1659457666760761088241997417004217632799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-82455265008376932706068986220000000000000)
      constant := (1457781580537350620924447388022894559180025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree058.table
  base := (-8297494602092144740426972877649912866681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14210000000000000000000000000000000000000000
      center := (37884)
      previous := (0)
      next := (24640)
      square := (321544946380135214999973498340000000000000)
      linear := (-23654274278612816993921930568300000000000000)
      constant := (422373471040447637682938337113699473816446299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (720558056186726821/195312500000000000)
  centralHi := (368925724767604132353/100000000000000000000)
  directionLo := (372147844675975467349/100000000000000000000)
  directionHi := (7442956893519509347/2000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree059.table
  base := (-104066226902237560997788118950231091181/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-20953237377759400539289913865000000000000)
      constant := (376880498950324746047587667092976890881900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree059.table
  base := (-333018801046260940750416377188246584741/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-697273962195416444665163626565220000000000000)
      constant := (12666740613291796598642993949040958662235203275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372147844675975467349/100000000000000000000)
  centralHi := (7442956893519509347/2000000000000000000)
  directionLo := (75068461073515001653/20000000000000000000)
  directionHi := (187671152683787504133/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree060.table
  base := (-8348931092955646109207898027239413573091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-85170634013698271608250324700000000000000)
      constant := (1558098906154836540173049419863802932134545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree060.table
  base := (-8349074266633257977843644401467703172741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-708573970311061196506591266649740000000000000)
      constant := (13091677501461992695274607923684317419954516131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75068461073515001653/20000000000000000000)
  centralHi := (187671152683787504133/50000000000000000000)
  directionLo := (378509807138887607083/100000000000000000000)
  directionHi := (94627451784721901771/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree061.table
  base := (-836819740733541003654369729330357159299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-43264159258179470529670496970000000000000)
      constant := (804756130170977442168323909562741071017525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree061.table
  base := (-8368316640137087915228217092561064018459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-719873978426705948348018906734260000000000000)
      constant := (13523640940755192970382752317229051112863323069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378509807138887607083/100000000000000000000)
  centralHi := (94627451784721901771/25000000000000000000)
  directionLo := (190825510612437414083/50000000000000000000)
  directionHi := (381651021224874828167/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree062.table
  base := (-8383105510778168511991735010119224718229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-87886003019019610510431663180000000000000)
      constant := (1661762016285354657430339427677403876408855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree062.table
  base := (-838320477934608921939763637355976748159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-365586993271175350094723273409390000000000000)
      constant := (6981315308318183297339455106313847770925578845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190825510612437414083/50000000000000000000)
  centralHi := (381651021224874828167/100000000000000000000)
  directionLo := (384766591459889902753/100000000000000000000)
  directionHi := (192383295729944951377/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree063.table
  base := (-4196831156593301479980254222673170961333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-44621843760840139980761166210000000000000)
      constant := (857424069717761226166040879590634145193335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree063.table
  base := (-4196872469423088622892366517568042680667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (78474)
      previous := (0)
      next := (51040)
      square := (666057388930280088214230817990000000000000)
      linear := (-53033856761285389430776727635950000000000000)
      constant := (1029189019382877327305789291844816932738913371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384766591459889902753/100000000000000000000)
  centralHi := (192383295729944951377/50000000000000000000)
  directionLo := (387857135818504422561/100000000000000000000)
  directionHi := (193928567909252211281/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree064.table
  base := (-8399873489660196347489751302720064100927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-90601372024340949412613001660000000000000)
      constant := (1768770601416960854206676145118399679495365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree064.table
  base := (-1679988449076729011668990213329380576351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-753774002773640203872301826987820000000000000)
      constant := (14861687693658852942316632045470867779145758205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387857135818504422561/100000000000000000000)
  centralHi := (193928567909252211281/50000000000000000000)
  directionLo := (390923247846691449707/100000000000000000000)
  directionHi := (97730811961672862427/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree065.table
  base := (-840174370251713024302670157721790361171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-45979528263500809431851835450000000000000)
      constant := (911764689459039477605943197756955240970725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree065.table
  base := (-1680360180526386409594674498609065322459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-765074010889284955713729467072340000000000000)
      constant := (15321754710302898910926260656391695135633935345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390923247846691449707/100000000000000000000)
  centralHi := (97730811961672862427/25000000000000000000)
  directionLo := (615571090613676261/156250000000000000)
  directionHi := (393965497992752807041/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree066.table
  base := (-839927678335666027434283753812588681019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-46658370514831144157397170070000000000000)
      constant := (939562226390440238604427559510685282974525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree066.table
  base := (-839932435874155351048650729931408630501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-388187009502464853777578553578430000000000000)
      constant := (7894423589598792951642316679309382908728421455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615571090613676261/156250000000000000)
  centralHi := (393965497992752807041/100000000000000000000)
  directionLo := (198492217423221458211/50000000000000000000)
  directionHi := (396984434846442916423/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree067.table
  base := (-524529742647205873171564323118866961591/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-23668606383080739441471252345000000000000)
      constant := (483888951813620720637761991429622660768180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree067.table
  base := (-4196257721719429889743431687668228688963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-393837013560287229698292373620690000000000000)
      constant := (8131482491866360374247162202258939963956523733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198492217423221458211/50000000000000000000)
  centralHi := (396984434846442916423/100000000000000000000)
  directionLo := (39998058629391207711/10000000000000000000)
  directionHi := (399980586293912077111/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree068.table
  base := (-8381343590695141745434849216015580743333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-96032110034983627216975678620000000000000)
      constant := (1992823429382975619172457071887922096283335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree068.table
  base := (-8381376480209316212459205248261742172211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-798974035236219211238012387325900000000000000)
      constant := (16744108028159790904638744132689741866825356901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39998058629391207711/10000000000000000000)
  centralHi := (399980586293912077111/100000000000000000000)
  directionLo := (402954460595355130533/100000000000000000000)
  directionHi := (201477230297677565267/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree069.table
  base := (-1045735255120122084228253841656360288897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-24347448634411074167016586965000000000000)
      constant := (512731827125858705424003443061436397111030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree069.table
  base := (-8365909378094622144128319105837985579361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-810274043351863963079440027410420000000000000)
      constant := (17232276233809096983833218829123442452260112551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402954460595355130533/100000000000000000000)
  centralHi := (201477230297677565267/50000000000000000000)
  directionLo := (405906547391595514629/100000000000000000000)
  directionHi := (40590654739159551463/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree070.table
  base := (-8346092989471856457288866717429260998521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-98747479040304966119157017100000000000000)
      constant := (2109867435834265201614866601812853695007395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree070.table
  base := (-4173057853404784255358910405225899917811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (78474)
      previous := (0)
      next := (51040)
      square := (666057388930280088214230817990000000000000)
      linear := (-58683860819107765351490547678210000000000000)
      constant := (1266247823999590154741922107696135127183846643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405906547391595514629/100000000000000000000)
  centralHi := (40590654739159551463/10000000000000000000)
  directionLo := (102209329661312456293/25000000000000000000)
  directionHi := (408837318645249825173/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree071.table
  base := (-1664395576759844109471030624580292254937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-100105163542965635570247686340000000000000)
      constant := (2169643804137609561671356580817492693626575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree071.table
  base := (-166439935164216208005449928689799361093/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-416437029791576733381147653789730000000000000)
      constant := (9114843940739582776388289289650051453217964075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102209329661312456293/25000000000000000000)
  centralHi := (408837318645249825173/100000000000000000000)
  directionLo := (411747229521595573303/100000000000000000000)
  directionHi := (51468403690199446663/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree072.table
  base := (-8293537918137960329322857668840021685337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-101462848045626305021338355580000000000000)
      constant := (2230256407442493444938993870663799891573315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree072.table
  base := (-8293553596598488725308381246790849173289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-844174067698798218603722947663980000000000000)
      constant := (18738931226405062636138352746392515896417933599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411747229521595573303/100000000000000000000)
  centralHi := (51468403690199446663/12500000000000000000)
  directionLo := (414636719213797404929/100000000000000000000)
  directionHi := (41463671921379740493/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree073.table
  base := (-8260774078716933414353249875854309479953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-102820532548286974472429024820000000000000)
      constant := (2291705240817772563361972123748728452600235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree073.table
  base := (-51629919374253800656884465891526299673/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 103022500000000000000000000000000000000000000
      center := (274659)
      previous := (0)
      next := (178640)
      square := (2331200861255980308749807862965000000000000)
      linear := (-213868518953610742611287646937125000000000000)
      constant := (4813799883648560613529121426425883708671013720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414636719213797404929/100000000000000000000)
  centralHi := (41463671921379740493/10000000000000000000)
  directionLo := (8350124234334563119/2000000000000000000)
  directionHi := (417506211716728155951/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree074.table
  base := (-8223687181041782406625915356747109203821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-104178217050947643923519694060000000000000)
      constant := (2353990300185918703919393412008264453980895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree074.table
  base := (-8223697993261047266553120357848537917679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-866774083930087722286578227833020000000000000)
      constant := (19778492776161778368254104915941939600950366089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8350124234334563119/2000000000000000000)
  centralHi := (417506211716728155951/100000000000000000000)
  directionLo := (26272257284577820283/6250000000000000000)
  directionHi := (420356116553245124529/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree075.table
  base := (-4091138950220083615791960444816915398987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-52767950776804156687305181650000000000000)
      constant := (1208555791085146783492021200775915423005065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree075.table
  base := (-8182286876810137190145970894659315438267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-878074092045732474128005867917540000000000000)
      constant := (20308810926379372109176495817424984270104455197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26272257284577820283/6250000000000000000)
  centralHi := (420356116553245124529/100000000000000000000)
  directionLo := (423186829456443935599/100000000000000000000)
  directionHi := (1057967073641109839/250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree076.table
  base := (-813654679711487196408714900930514170057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (66)
      previous := (0)
      next := (44)
      square := (565701876108612271287778850000000000000)
      linear := (-53446793028134491412850516270000000000000)
      constant := (1240534541984941616090809839852737145748575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree076.table
  base := (-8136554248029694116636854300493606618259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1098636)
      previous := (0)
      next := (714560)
      square := (9324803445023921234999231451860000000000000)
      linear := (-889374100161377225969433508002060000000000000)
      constant := (20846153964745471331418311927385758964868164869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423186829456443935599/100000000000000000000)
  centralHi := (1057967073641109839/250000000000000000)
  directionLo := (425998733011108061811/100000000000000000000)
  directionHi := (106499683252777015453/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree077.table
  base := (-2021623584173310545266974678109098506309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12500000000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (22)
      square := (282850938054306135643889425000000000000)
      linear := (-27062817639732413069197925445000000000000)
      constant := (636465700814137742906865937871454507468455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree077.table
  base := (-2021625130080564987084538294923328597503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14717500000000000000000000000000000000000000
      center := (39237)
      previous := (0)
      next := (25520)
      square := (333028694465140044107115408995000000000000)
      linear := (-32166932438465070636102183860235000000000000)
      constant := (763947209793720381633112938252926364546499839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425998733011108061811/100000000000000000000)
  centralHi := (106499683252777015453/25000000000000000000)
  directionLo := (214396098628648846023/50000000000000000000)
  directionHi := (428792197257297692047/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree078.table
  base := (-8032120907083470269799103229383727979207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (132)
      previous := (0)
      next := (88)
      square := (1131403752217224542575557700000000000000)
      linear := (-109608955061590321727882371020000000000000)
      constant := (2611492738090755823385209950741081360103965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree078.table
  base := (-4016063019054458144411425667796568762487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (549318)
      previous := (0)
      next := (357280)
      square := (4662401722511960617499615725930000000000000)
      linear := (-455987058196333364826144394085550000000000000)
      constant := (10970957320311110910150703879480951197866673217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell289.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell289
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 78 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 78 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 78 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel078.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell289

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel079
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  degreePropagationTail 79 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel080
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  degreePropagationTail 80 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel081
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  degreePropagationTail 81 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel082
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  degreePropagationTail 82 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel083
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  degreePropagationTail 83 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel084
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  degreePropagationTail 84 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel085
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  degreePropagationTail 85 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel086
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  degreePropagationTail 86 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel087
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  degreePropagationTail 87 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel088
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  degreePropagationTail 88 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel089
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  degreePropagationTail 89 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel090
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  degreePropagationTail 90 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel091
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  degreePropagationTail 91 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel092
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  degreePropagationTail 92 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel093
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  degreePropagationTail 93 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel094
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  degreePropagationTail 94 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel095
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  degreePropagationTail 95 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel096
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  degreePropagationTail 96 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel097
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  degreePropagationTail 97 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel098
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  degreePropagationTail 98 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel099
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  degreePropagationTail 99 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel100
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  degreePropagationTail 100 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel101
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  degreePropagationTail 101 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel102
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  degreePropagationTail 102 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel103
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  degreePropagationTail 103 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell289.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 78 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell289.Kernel349

