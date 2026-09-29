import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell170.Parameters
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch000_049
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch050_099
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch000_049
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree000.table
  base := (87841263293687917947920597/2000000000000000000000000)
  polynomial :=
    { denominator := 18992500000000000000000000000000000000000000
      center := (97053)
      previous := (0)
      next := (85275)
      square := (3727196179868628845149869431800000000000000)
      linear := (-14860397192447633299416942434575000000000000)
      constant := (834162596552683890812940969261250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree000.table
  base := (87841263293687917947920597/2000000000000000000000000)
  polynomial :=
    { denominator := 9496250000000000000000000000000000000000000
      center := (48539)
      previous := (0)
      next := (42625)
      square := (1863598089934314422574934715900000000000000)
      linear := (-7430198596223816649708471217287500000000000)
      constant := (417081298276341945406470484630625000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree001.table
  base := (4013136444110764557272139683264833192257/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-143039068374757173118031368172506725000000000000)
      constant := (3773969335872807814336090896401105048295138097808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree001.table
  base := (256793745777079748018223351270100436585611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-5149686001204748379412515494417627100000000000000)
      constant := (135839195915624048302433411046079811738624650920091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49894679346064433991/100000000000000000000)
  directionHi := (6236834918258054249/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree002.table
  base := (157260904136598198968799275173765181331427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-692734797113958704241568898678188700000000000000)
      constant := (9685336489738609386412978783819252920321142431643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree002.table
  base := (39302393841511884095056850995942938928317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-1558793063363152158125223142129617075000000000000)
      constant := (21785769130486976681891028845540016299238181176877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49894679346064433991/100000000000000000000)
  centralHi := (6236834918258054249/12500000000000000000)
  directionLo := (35280866110730535851/50000000000000000000)
  directionHi := (70561732221461071703/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree003.table
  base := (101355562330895468554686112060274467756237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-813313320728888716011012324666350500000000000000)
      constant := (6859626631161314760304433158999113559340774518933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree003.table
  base := (10131230399370167342267429314209950413347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-406703250316692715866070535701072750000000000000)
      constant := (3428732287308409068113564799812975587628139084615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/50000000000000000000)
  centralHi := (70561732221461071703/100000000000000000000)
  directionLo := (21605029913685271329/25000000000000000000)
  directionHi := (86420119654741085317/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree004.table
  base := (68685569855427748006506988674817360113837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-933891844343818727780455750654512300000000000000)
      constant := (5439115046645237398514880706482998171910275177333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree004.table
  base := (68651809123472523418119772398544440727241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-8406144757948329138677646716720150700000000000000)
      constant := (48939109238853141077680996264432004411274200640121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21605029913685271329/25000000000000000000)
  centralHi := (86420119654741085317/100000000000000000000)
  directionLo := (49894679346064433991/50000000000000000000)
  directionHi := (99789358692128867983/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree005.table
  base := (388374363055493228762988117647166525537/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-1054470367958748739549899176642674100000000000000)
      constant := (4806019122721559684836311752481471318243920329125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree005.table
  base := (48520704020510156608464393959748480226493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-9491631010196189391766023790820991900000000000000)
      constant := (43247126247826509685352601651975252549282066738733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49894679346064433991/50000000000000000000)
  centralHi := (99789358692128867983/100000000000000000000)
  directionLo := (111567894733354828469/100000000000000000000)
  directionHi := (11156789473335482847/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree006.table
  base := (4414178733689067279312922928866864743571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-293762222893419687829835650657708975000000000000)
      constant := (1158912153861831128814128438211098682966273629078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree006.table
  base := (137862334131710826849039004576848286897/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (368750783)
      previous := (0)
      next := (323822125)
      square := (14157754689230986668301779036692300000000000000)
      linear := (-146904406422834022845200012012803237500000000000)
      constant := (579427788173650240958933831257738662999529563936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111567894733354828469/100000000000000000000)
  centralHi := (11156789473335482847/10000000000000000000)
  directionLo := (122216505277640519213/100000000000000000000)
  directionHi := (61108252638820259607/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree007.table
  base := (13005624237418929811843306000747805289173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-647813707594304381544393014309498850000000000000)
      constant := (2378173947878671168293183485786985852811693793757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree007.table
  base := (25994179082045285370294290752012874242101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-11662603514691909897942777939022674300000000000000)
      constant := (42809457641772946855272062194557229950467639199781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122216505277640519213/100000000000000000000)
  centralHi := (61108252638820259607/50000000000000000000)
  directionLo := (5280356531799893029/4000000000000000000)
  directionHi := (66004456647498662863/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree008.table
  base := (9526333034463380123749235742893550333137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-708102969401769387429114727303579750000000000000)
      constant := (2538245213097502806482462397193347657388755071033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree008.table
  base := (19037942836374143840834602983030642223163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-12748089766939770151031155013123515500000000000000)
      constant := (45694748613712555091971310419927035503202687901003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5280356531799893029/4000000000000000000)
  centralHi := (66004456647498662863/50000000000000000000)
  directionLo := (35280866110730535851/25000000000000000000)
  directionHi := (28224692888584428681/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree009.table
  base := (13577105784496773327910944049703342911967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-1536784462418468786627672880595321300000000000000)
      constant := (5546408521466035338236165986545675111488514432503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree009.table
  base := (3390982642084886283362183355967684163243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737501566)
      previous := (0)
      next := (647644250)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-384266000532989733447764780200676575000000000000)
      constant := (1386886186812833478330426527824639495830229268387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/25000000000000000000)
  centralHi := (28224692888584428681/20000000000000000000)
  directionLo := (74842019019096650987/50000000000000000000)
  directionHi := (5987361521527732079/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree010.table
  base := (1138348097752064517114609647352874730117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-414340746508349699599279076645870775000000000000)
      constant := (1534631806839133980325087498227054877749474311706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree010.table
  base := (9094680409662138636256101197402053646629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-14919062271435490657207909161325197900000000000000)
      constant := (55260912110491290131827911004734279504413388195349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74842019019096650987/50000000000000000000)
  centralHi := (5987361521527732079/4000000000000000000)
  directionLo := (15778082985732420131/10000000000000000000)
  directionHi := (157780829857324201311/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree011.table
  base := (214675553350904815539192887899957035659/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-1777941509648328810166559732571644900000000000000)
      constant := (6836985803129238890129540225700521160961277763275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree011.table
  base := (5355583961280312427410349693907148112623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-16004548523683350910296286235426039100000000000000)
      constant := (61551137016275916047858528484271034462759516963263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15778082985732420131/10000000000000000000)
  centralHi := (157780829857324201311/100000000000000000000)
  directionLo := (1292827581453053533/781250000000000000)
  directionHi := (6619277217039634089/4000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree012.table
  base := (109572479053363170850535603502249424921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-474630008315814705484000789639951675000000000000)
      constant := (1908051370762299849998114761024143166149526933445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree012.table
  base := (2180796885307806092594193709905826844527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-1898892752881245684820518145502986700000000000000)
      constant := (7634714774565774056299494683807505541988210689543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1292827581453053533/781250000000000000)
  centralHi := (6619277217039634089/4000000000000000000)
  directionLo := (172840239309482170633/100000000000000000000)
  directionHi := (86420119654741085317/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree013.table
  base := (-526074808724605586079207484897311004489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2019098556878188833705446584547968500000000000000)
      constant := (8518037268212685724876434370701548669686721017999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree013.table
  base := (-107230391310743653555817616374090455937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-18175521028179071416473040383627721500000000000000)
      constant := (76689495705537428970326141323864830314037497669515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172840239309482170633/100000000000000000000)
  centralHi := (86420119654741085317/50000000000000000000)
  directionLo := (17989782475506938321/10000000000000000000)
  directionHi := (179897824755069383211/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree014.table
  base := (-114355251566041692492045534001555141181/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2139677080493118845474890010536130300000000000000)
      constant := (9490256639705071377446810871975101923645675574275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree014.table
  base := (-1434210818212277983468683235971385425581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-9630503640213465834780708728864281350000000000000)
      constant := (42722162113059301225287423994016646268262411930339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17989782475506938321/10000000000000000000)
  centralHi := (179897824755069383211/100000000000000000000)
  directionLo := (93344397767959598371/50000000000000000000)
  directionHi := (186688795535919196743/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree015.table
  base := (-2430351369265133361240535142332465891561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1130127802054024428622166718262146050000000000000)
      constant := (5272881218105175689366256698560016912055898797551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree015.table
  base := (-4869726415650498071205742227237829636307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2260721503630532435849977170203267100000000000000)
      constant := (10549890861244388007018630579235038335097856552437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93344397767959598371/50000000000000000000)
  centralHi := (186688795535919196743/100000000000000000000)
  directionLo := (48310315542916680617/25000000000000000000)
  directionHi := (193241262171666722469/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree016.table
  base := (-657329529451520037122925848905324924697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1190417063861489434506888431256226950000000000000)
      constant := (5841072363460882357042924920956567875090715704635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree016.table
  base := (-6581814609640406196036519870508964266893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-21431979784922652175738171605930245100000000000000)
      constant := (105181890966624985434617087790142365383207370148867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48310315542916680617/25000000000000000000)
  centralHi := (193241262171666722469/100000000000000000000)
  directionLo := (39915743476851547193/20000000000000000000)
  directionHi := (99789358692128867983/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree017.table
  base := (-4015281243704707585315552660172063380387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1250706325668954440391610144250307850000000000000)
      constant := (6448723394812413570005905625892424298690422103717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree017.table
  base := (-8038587639529851256633057754631595912729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-22517466037170512428826548680031086300000000000000)
      constant := (116125334468029186306686127239751588187530271690551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39915743476851547193/20000000000000000000)
  centralHi := (99789358692128867983/50000000000000000000)
  directionLo := (642878228437961139/312500000000000000)
  directionHi := (205721033100147564481/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree018.table
  base := (-9260899062311429521376396552000025119139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2621991174952838892552663714488777500000000000000)
      constant := (14190029838387472020238961448483178557263738026149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree018.table
  base := (-4634220456715859633279569654040943962497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1311275127189909593439718097451773750000000000000)
      constant := (7098033268757452971408888659029808532402367480727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642878228437961139/312500000000000000)
  centralHi := (205721033100147564481/100000000000000000000)
  directionLo := (105842598332191607553/50000000000000000000)
  directionHi := (211685196664383215107/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree019.table
  base := (-2572145699707180210279593194279788298503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-685642424641942226080526785119234825000000000000)
      constant := (3889623173876955385906649371060663256456783770273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree019.table
  base := (-10295654007071141281442957692605940770129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-24688438541666232935003302828232768700000000000000)
      constant := (140087072543166166802730548029885103202066999201151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105842598332191607553/50000000000000000000)
  centralHi := (211685196664383215107/100000000000000000000)
  directionLo := (108742932544930463027/50000000000000000000)
  directionHi := (43497173017972185211/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree020.table
  base := (-11134649040357573088606686071942815213927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2863148222182698916091550566465101100000000000000)
      constant := (17001621318573647128699302810527382188131994625857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree020.table
  base := (-5570632160856348681807698795722664505137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-12886962396957046594045839951166804950000000000000)
      constant := (76540914066998648220211146097166639961626665228703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108742932544930463027/50000000000000000000)
  centralHi := (43497173017972185211/20000000000000000000)
  directionLo := (223135789466709656939/100000000000000000000)
  directionHi := (11156789473335482847/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree021.table
  base := (-11817477169037333438832588729179070788251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2983726745797628927860993992453262900000000000000)
      constant := (18518354952406991197606637721093825374286929391341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree021.table
  base := (-11823653127949281963987734908186322833099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-2984379005129105937908895219603827900000000000000)
      constant := (18526590870289677839214634905997586740804485576509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223135789466709656939/100000000000000000000)
  centralHi := (11156789473335482847/5000000000000000000)
  directionLo := (228646144878890020401/100000000000000000000)
  directionHi := (114323072439445010201/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree022.table
  base := (-12353210846712431521380039503815565480001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-3104305269412558939630437418441424700000000000000)
      constant := (20107761875105406644335075120517494818320940965591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree022.table
  base := (-12358965620409132954901171732331591877917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-27944897298409813694268434050535292300000000000000)
      constant := (181051155345700150628636504584313200294631381745523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228646144878890020401/100000000000000000000)
  centralHi := (114323072439445010201/50000000000000000000)
  directionLo := (234026790336117189411/100000000000000000000)
  directionHi := (58506697584029297353/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree023.table
  base := (-1594509695258897772130514797480572506943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-806220948256872237849970211107396625000000000000)
      constant := (5442255238891923298160549469353636643810272716626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree023.table
  base := (-3190357602462969263565820713331381812559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-7257595887664418486839202781159033375000000000000)
      constant := (49002487477632125148443713731243324141563276836321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234026790336117189411/100000000000000000000)
  centralHi := (58506697584029297353/25000000000000000000)
  directionLo := (119643238026717939889/50000000000000000000)
  directionHi := (239286476053435879779/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree024.table
  base := (-13038643427438631313246795127630064084213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-3345462316642418963169324270417748300000000000000)
      constant := (23501406948047583202083278292872559580747520474883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree024.table
  base := (-6521807165696837663175164007532414693683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1673103877939196344469177122152054150000000000000)
      constant := (11756065218885365739376951504517398037611169621653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119643238026717939889/50000000000000000000)
  centralHi := (239286476053435879779/100000000000000000000)
  directionLo := (122216505277640519213/50000000000000000000)
  directionHi := (244433010555281038427/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree025.table
  base := (-6606011755521777451637678781375534967201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1733020420128674487469383848202955050000000000000)
      constant := (12652139176475629095283320381701243917309159900791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree025.table
  base := (-660831640934981317619207111025783254351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-7800339013788348613383391318209453975000000000000)
      constant := (56960763436940389989197427676876863638336591039845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122216505277640519213/50000000000000000000)
  centralHi := (244433010555281038427/100000000000000000000)
  directionLo := (249473396730322169957/100000000000000000000)
  directionHi := (124736698365161084979/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree026.table
  base := (-3321514906849572039074800015541175237473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-896654840968069746677052780598517975000000000000)
      constant := (6794266788942662777071295577912582224753811151543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree026.table
  base := (-13290327747374471190590219105291598915599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-32286842307401254706621942346938657100000000000000)
      constant := (244706477171697618207826935218341882113290465506081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249473396730322169957/100000000000000000000)
  centralHi := (124736698365161084979/50000000000000000000)
  directionLo := (63603485902509359423/25000000000000000000)
  directionHi := (254413943610037437693/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree027.table
  base := (-6634736486804357528696901247464466795279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-1853598943743604499238827274191116850000000000000)
      constant := (14559635008884511675308853398291002137910348524889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree027.table
  base := (-13273420125344004287372403627495903795727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-3708036506627679439967813269004388700000000000000)
      constant := (29132768251264429353436631092228378437508759469657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63603485902509359423/25000000000000000000)
  centralHi := (254413943610037437693/100000000000000000000)
  directionLo := (259260358964223255949/100000000000000000000)
  directionHi := (5185207179284465119/2000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree028.table
  base := (-13169996483306538561325445490255259531817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-3827776411102139010247097974370395500000000000000)
      constant := (31130440637251984957866324598554424586979565148847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree028.table
  base := (-2634728499420648783122766952877552746489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-34457814811896975212798696495140339500000000000000)
      constant := (280304348503687932228525084713411621824152724299955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259260358964223255949/100000000000000000000)
  centralHi := (5185207179284465119/2000000000000000000)
  directionLo := (5280356531799893029/2000000000000000000)
  directionHi := (264017826589994651451/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree029.table
  base := (-3248622581574027394685244346224878407431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-987088733679267255504135350089639325000000000000)
      constant := (8302545770893409542898610264524773461618258626721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree029.table
  base := (-3249463621982633107108661612214314762797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-8885825266036208866471768392310295175000000000000)
      constant := (74757804201412928361480792336243039985376763622243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5280356531799893029/2000000000000000000)
  centralHi := (264017826589994651451/100000000000000000000)
  directionLo := (134345535638843499697/50000000000000000000)
  directionHi := (53738214255537399879/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree030.table
  base := (-12749043115089694819598588863244202804947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4068933458331999033785984826346719100000000000000)
      constant := (35358145956061207513386444785157570137436341618677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree030.table
  base := (-6376072024363718917478824520518402568667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-2034932628688483095498636146852334550000000000000)
      constant := (17687353161382025705541414847197219147125302177197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134345535638843499697/50000000000000000000)
  centralHi := (53738214255537399879/20000000000000000000)
  directionLo := (273284413773266009199/100000000000000000000)
  directionHi := (683211034433165023/250000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree031.table
  base := (-12439060828443929511374243821940053951351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4189511981946929045555428252334880900000000000000)
      constant := (37574017251845687226259979961729319677769662283441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree031.table
  base := (-6220958205908694526367886769020301133643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-18857136784320277986031913858721431550000000000000)
      constant := (169162480581630345209260642089349467487127878142117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273284413773266009199/100000000000000000000)
  centralHi := (683211034433165023/250000000000000000)
  directionLo := (277801817557848698187/100000000000000000000)
  directionHi := (69450454389462174547/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree032.table
  base := (-2413869017755479605483702108692429461167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4310090505561859057324871678323042700000000000000)
      constant := (39857519848126947562490483189577148154372790723485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree032.table
  base := (-6035986197566228078272914820194258684883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-19399879910444208112576102395771852150000000000000)
      constant := (179443267946738701181819827861740195453279743787677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277801817557848698187/100000000000000000000)
  centralHi := (69450454389462174547/25000000000000000000)
  directionLo := (35280866110730535851/12500000000000000000)
  directionHi := (282246928885844286809/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree033.table
  base := (-2328832432239072027734429727482570005493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4430669029176789069094315104311204500000000000000)
      constant := (42208407519935801131606633153821784221659223756815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree033.table
  base := (-11646577423178767152725332264772373519501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4431694008126252942026731318404949500000000000000)
      constant := (42228318389715116764691502281376037467794749810091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/12500000000000000000)
  centralHi := (282246928885844286809/100000000000000000000)
  directionLo := (143311555616197111039/50000000000000000000)
  directionHi := (286623111232394222079/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree034.table
  base := (-11167303836773684094532755973231413040723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4551247552791719080863758530299366300000000000000)
      constant := (44626461426291252723432582887408882351119779122293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree034.table
  base := (-11169522428103303046538340140053173990801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-40970732325384136731328958939745386700000000000000)
      constant := (401827980882460836985595509259113237460920739635519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143311555616197111039/50000000000000000000)
  centralHi := (286623111232394222079/100000000000000000000)
  directionLo := (290933475075633088773/100000000000000000000)
  directionHi := (145466737537816544387/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree035.table
  base := (-2660535299892245442051774951042134133661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1167956519101662273158300489071882025000000000000)
      constant := (11777871751767321415290955220879131263127028378651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree035.table
  base := (-5322088815477291540209593335865222433023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-21028109288815998492208668006923113950000000000000)
      constant := (212102065712853814419067797219700414590120819244337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290933475075633088773/100000000000000000000)
  centralHi := (145466737537816544387/50000000000000000000)
  directionLo := (295180903763489769053/100000000000000000000)
  directionHi := (147590451881744884527/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree036.table
  base := (-5035836071402075810817989919247220905049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-2396202300010789552201322691137844950000000000000)
      constant := (24831655620317147627401212446997262045572651848959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree036.table
  base := (-5036770034573012172200217110158423401439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-2396761379437769846528095171552614950000000000000)
      constant := (24843431132610490563091567440372967447014178365449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295180903763489769053/100000000000000000000)
  centralHi := (147590451881744884527/50000000000000000000)
  directionLo := (74842019019096650987/25000000000000000000)
  directionHi := (299368076076386603949/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree037.table
  base := (-9458563387203867942964488143115747546689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-4912983123636509116172088808263851700000000000000)
      constant := (52281780218775688876090605223950775511749644458199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree037.table
  base := (-9460275623585160453153089196628054197149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-44227191082127717490594090162047910300000000000000)
      constant := (470759483028635056702168029941132051357724183820531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74842019019096650987/25000000000000000000)
  centralHi := (299368076076386603949/100000000000000000000)
  directionLo := (60699497197497043561/20000000000000000000)
  directionHi := (151748742993742608903/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree038.table
  base := (-880518765869476292301792915870574892257/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-2516780823625719563970766117126006750000000000000)
      constant := (27483378500509445985387252102673372260515742844435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree038.table
  base := (-8806756203103894210294938464480103214249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-45312677334375577743682467236148751500000000000000)
      constant := (494936067310798392181788849806058787006575567275431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60699497197497043561/20000000000000000000)
  centralHi := (151748742993742608903/50000000000000000000)
  directionLo := (307571460034526569769/100000000000000000000)
  directionHi := (30757146003452656977/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree039.table
  base := (-202841415009710101710176968650984360829/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1288535042716592284927743915060043825000000000000)
      constant := (14429529928782425374786619329086584959715115149390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree039.table
  base := (-8115092661466200001092044229058800220499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-5155351509624826444085649367805510300000000000000)
      constant := (57745601865931286412253305747791977894024830529909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307571460034526569769/100000000000000000000)
  centralHi := (30757146003452656977/10000000000000000000)
  directionLo := (77898043161725572547/25000000000000000000)
  directionHi := (311592172646902290189/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree040.table
  base := (-1846462480650965098133053933908871570783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1318679673620324787870104771557084275000000000000)
      constant := (15133939968684490297916978595952738542435357487753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree040.table
  base := (-295486558040540256391228930123764960267/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-47483649838871298249859221384350433900000000000000)
      constant := (545081555492769290835046584068659307904238362879325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77898043161725572547/25000000000000000000)
  centralHi := (311592172646902290189/100000000000000000000)
  directionLo := (15778082985732420131/5000000000000000000)
  directionHi := (315561659714648402621/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree041.table
  base := (-264937649316080659479388209968802472777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-5395297218096229163249862512216498900000000000000)
      constant := (63419580888572396662617913400236959671148421405175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree041.table
  base := (-6624642955175728185567937680245878044851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-48569136091119158502947598458451275100000000000000)
      constant := (571048614463655180752051579472393019690598141377469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15778082985732420131/5000000000000000000)
  centralHi := (315561659714648402621/100000000000000000000)
  directionLo := (319481830639725334271/100000000000000000000)
  directionHi := (1247975900936427087/390625000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree042.table
  base := (-291396046715445647242214601029572555173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1378968935427789793754826484551165175000000000000)
      constant := (16592374184725797041889216852110580561027852061215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree042.table
  base := (-5829019388240147062142444717908481350807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-5517180260374113195115108392505790700000000000000)
      constant := (66401202211580247063111962203533955832750652321937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319481830639725334271/100000000000000000000)
  centralHi := (1247975900936427087/390625000000000000)
  directionLo := (16167723953602492947/5000000000000000000)
  directionHi := (323354479072049858941/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree043.table
  base := (-5000616532971499341060373842546396741379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-5636454265326089186788749364192822500000000000000)
      constant := (69385430809497620644613770709909873431991785169989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree043.table
  base := (-1000324020760316577372358135000285733291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-50740108595614879009124352606652957500000000000000)
      constant := (624767482607330928306349426174712275708239023949145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16167723953602492947/5000000000000000000)
  centralHi := (323354479072049858941/100000000000000000000)
  directionLo := (40897661562697284119/12500000000000000000)
  directionHi := (327181292501578272953/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree044.table
  base := (-25891941596733366771276508384281121277/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1439258197235254799639548197545246075000000000000)
      constant := (18116828711440281302011210214742423195325624788280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree044.table
  base := (-2071813556137924714478546507281407925927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-25912797423931369631106364840376899350000000000000)
      constant := (326258994300844035071784875771006815953804866760713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40897661562697284119/12500000000000000000)
  centralHi := (327181292501578272953/100000000000000000000)
  directionLo := (1292827581453053533/390625000000000000)
  directionHi := (330963860851981704449/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree045.table
  base := (-813814260046864838688524113348549661027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1469402828138987302581909054042286525000000000000)
      constant := (18903772007951738619025009177975908695306676361957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree045.table
  base := (-50876462061735785374647633569671137387/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (368750783)
      previous := (0)
      next := (323822125)
      square := (14157754689230986668301779036692300000000000000)
      linear := (-734876126390424993268070927150758887500000000000)
      constant := (9456413761744722168835263460790053287975811925736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1292827581453053533/390625000000000000)
  centralHi := (330963860851981704449/100000000000000000000)
  directionLo := (10459490131252015169/3125000000000000000)
  directionHi := (334703684200064485409/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree046.table
  base := (-467838947100654988740213610466609596693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-5998189836170879222097079642157307900000000000000)
      constant := (78828696171011598468749252123102549189465675752815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree046.table
  base := (-1142557610645579964608687624002088799/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-6749570919044807471048685478619435137500000000000)
      constant := (88724800231551290334134513034390105231631249761536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10459490131252015169/3125000000000000000)
  centralHi := (334703684200064485409/100000000000000000000)
  directionLo := (16920108986361692867/5000000000000000000)
  directionHi := (338402179727233857341/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree047.table
  base := (-1395360710434976676991050246453278774387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-6118768359785809233866523068145469700000000000000)
      constant := (82108090958203282684363862820937875594424009957717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree047.table
  base := (-1396056815121748826688097975779963067041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-55082053604606320021477860903056322300000000000000)
      constant := (739327387140483230954190746741875107632895111756079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16920108986361692867/5000000000000000000)
  centralHi := (338402179727233857341/100000000000000000000)
  directionLo := (171030343997190798403/50000000000000000000)
  directionHi := (342060687994381596807/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree048.table
  base := (-212250529330529508006620136036961356913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3119673441700369622817983247066815750000000000000)
      constant := (42726614666513147089547508983965513873129928140583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree048.table
  base := (-42513567442950663142248203624314759077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3120418880936343348587013220953175750000000000000)
      constant := (42747131078571112117643932194088679278249467797535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171030343997190798403/50000000000000000000)
  centralHi := (342060687994381596807/100000000000000000000)
  directionLo := (172840239309482170633/50000000000000000000)
  directionHi := (345680478618964341267/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree049.table
  base := (286359521982210793230763090804914483401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3179962703507834628702704960060896650000000000000)
      constant := (44432036452624667507259206184921998748705029025009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree049.table
  base := (35758794020373597522958266397001235029/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-7156628263637755065956826881407250587500000000000)
      constant := (100020121674089026931035416614119241032360438991498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172840239309482170633/50000000000000000000)
  centralHi := (345680478618964341267/100000000000000000000)
  directionLo := (349262755422451037939/100000000000000000000)
  directionHi := (17463137771122551897/5000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree050.table
  base := (797853243580935775734312464409154866571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3240251965315299634587426673054977550000000000000)
      constant := (46170293721931573311231953954943702594813619121539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree050.table
  base := (1595179624928880762579239467998698419743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-58338512361349900780742992125358845900000000000000)
      constant := (831464921211773508105444922931583937378582310591983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349262755422451037939/100000000000000000000)
  centralHi := (17463137771122551897/5000000000000000000)
  directionLo := (35280866110730535851/10000000000000000000)
  directionHi := (352808661107305358511/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree051.table
  base := (660983088588089793106262500572652376159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1650270613561382320236074193024529225000000000000)
      constant := (23970685605689991414408676247304328512202462375031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree051.table
  base := (165215784731347543865719037775834701871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (368750783)
      previous := (0)
      next := (323822125)
      square := (14157754689230986668301779036692300000000000000)
      linear := (-825333314077746681025435683325828987500000000000)
      constant := (11991110115783655277335988177127066057975351918478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/10000000000000000000)
  centralHi := (352808661107305358511/100000000000000000000)
  directionLo := (356319281515014325409/100000000000000000000)
  directionHi := (35631928151501432541/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree052.table
  base := (464615615090766996710383468592846462149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1680415244465114823178435049521569675000000000000)
      constant := (24872627654155296712330035941961257402881340809882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree052.table
  base := (3716488129088100864636026082019128466053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-60509484865845621286919746273560528300000000000000)
      constant := (895845749924362027572227087790818882435019929119093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356319281515014325409/100000000000000000000)
  centralHi := (35631928151501432541/10000000000000000000)
  directionLo := (17989782475506938321/5000000000000000000)
  directionHi := (359795649510138766421/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree053.table
  base := (4814263423544717124026559141712085577943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-6842239501475389304483183624074440500000000000000)
      constant := (103163867741374029323931121184884601167288403680687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree053.table
  base := (2406932956740925973273298529869054770521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-30797485559046740770004061673830684750000000000000)
      constant := (464461083795467363375948270362166600203723251233801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17989782475506938321/5000000000000000000)
  centralHi := (359795649510138766421/100000000000000000000)
  directionLo := (363238748529764108319/100000000000000000000)
  directionHi := (2270242178311025677/625000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree054.table
  base := (5935572518183460594471882549002445893187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-6962818025090319316252627050062602300000000000000)
      constant := (106902792134225310539928285492866035129279764831483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree054.table
  base := (5935210870783752615718621388651805949721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-6964495263371260199232944491306912300000000000000)
      constant := (106954331836691235470354405026762794337170831229889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363238748529764108319/100000000000000000000)
  centralHi := (2270242178311025677/625000000000000000)
  directionLo := (9166237895823038941/2500000000000000000)
  directionHi := (366649515832921557641/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree055.table
  base := (3540258671656656100757872513919476981117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3541698274352624664011035238025382050000000000000)
      constant := (55353632234425663590290883295021603700054271814853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree055.table
  base := (1770047105768573421065364163286183386503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-15941485905647300511546219373965762975000000000000)
      constant := (249211508238129801178740948971896626991908752995543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9166237895823038941/2500000000000000000)
  centralHi := (366649515832921557641/100000000000000000000)
  directionLo := (185014422740203138461/50000000000000000000)
  directionHi := (370028845480406276923/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree056.table
  base := (412439956367492451956737118280011893281/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-1800993768080044834947878475509731475000000000000)
      constant := (28644316875456664571066090290529141289668419929645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree056.table
  base := (1031062507564384033937247105260804992183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-8106428734354632787409156821245486637500000000000)
      constant := (128961643975369855778419924004567372983892823183623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185014422740203138461/50000000000000000000)
  centralHi := (370028845480406276923/100000000000000000000)
  directionLo := (93344397767959598371/25000000000000000000)
  directionHi := (74675518214367678697/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree057.table
  base := (9440151276006133615312026734927510481731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-7324553595935109351560957328027087700000000000000)
      constant := (118512785846819590477204374618687161975294409961979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree057.table
  base := (9439879430307257909498803578078823637239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-7326324014120546950262403516007192700000000000000)
      constant := (118570022747776745978138532882958042586638479276751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93344397767959598371/25000000000000000000)
  centralHi := (74675518214367678697/20000000000000000000)
  directionLo := (376696568263709514803/100000000000000000000)
  directionHi := (94174142065927378701/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree058.table
  base := (10654335887596544087268917032736326677731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-7445132119550039363330400754015249500000000000000)
      constant := (122513805773474937990948344462091011022036178125979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree058.table
  base := (332940276667106783180891954718148272783/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-8377800297416597850681251089770696937500000000000)
      constant := (137894633534504241324346236460871359852719498688892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376696568263709514803/100000000000000000000)
  centralHi := (94174142065927378701/25000000000000000000)
  directionLo := (189993278544730465443/50000000000000000000)
  directionHi := (379986557089460930887/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree059.table
  base := (11891140648759556837064066134489957103081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-7565710643164969375099844180003411300000000000000)
      constant := (126580315028252517686547244046371625565639671994129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree059.table
  base := (18579556595693723890208865899277455389/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-8513486078947580382317298224033302087500000000000)
      constant := (142471704033211790977952370512938550602031000072720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189993278544730465443/50000000000000000000)
  centralHi := (379986557089460930887/100000000000000000000)
  directionLo := (95812076025072623687/25000000000000000000)
  directionHi := (383248304100290494749/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree060.table
  base := (6575188034296429216841251321894055045033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3843144583389949693434643802995786550000000000000)
      constant := (65356151337398445833798641013616929022537547980497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree060.table
  base := (13150172231684719485014880889590395773371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-7688152764869833701291862540707473100000000000000)
      constant := (130775533152192471956247038625420562444136205202739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95812076025072623687/25000000000000000000)
  centralHi := (383248304100290494749/100000000000000000000)
  directionLo := (386482524343333444937/100000000000000000000)
  directionHi := (193241262171666722469/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree061.table
  base := (7215936506953440625066970892930729894873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3903433845197414699319365515989867450000000000000)
      constant := (67454879475842990876770590835080099353821227325057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree061.table
  base := (14431687924859581966520553510604030457693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-70278861136076363564715139940468099100000000000000)
      constant := (1214775478825407457132707173379719927282953758985933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386482524343333444937/100000000000000000000)
  centralHi := (193241262171666722469/50000000000000000000)
  directionLo := (389689903192066188383/100000000000000000000)
  directionHi := (12177809474752068387/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree062.table
  base := (7867740256237710819704519433148781530951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-3963723107004879705204087228983948350000000000000)
      constant := (69586337572823488593289077014317673897628952172959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree062.table
  base := (15735312487817045076445321345125929256211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-71364347388324223817803517014568940300000000000000)
      constant := (1253160595295996654762173282496926195788382246998691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389689903192066188383/100000000000000000000)
  centralHi := (12177809474752068387/3125000000000000000)
  directionLo := (392871098042205831199/100000000000000000000)
  directionHi := (491088872552757289/125000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree063.table
  base := (17061063794858054371088384013852832536909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-8048024737624689422177617883956058500000000000000)
      constant := (143501043478541272563825854039811715567843673621781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree063.table
  base := (4265227824332216135706639262488284230723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737501566)
      previous := (0)
      next := (647644250)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2012495378904780113080330391351938375000000000000)
      constant := (35892641051505537177284612505988946637550197587707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392871098042205831199/100000000000000000000)
  centralHi := (491088872552757289/125000000000000000)
  directionLo := (15841069595399679087/4000000000000000000)
  directionHi := (49503342485623997147/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree064.table
  base := (2301062818580561135252629144223655628467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2042150815309904858486765327486055075000000000000)
      constant := (36973714251652303152864157397155936296832992962006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree064.table
  base := (18408364175114371471376637436758496518423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-73535319892819944323980271162770622700000000000000)
      constant := (1331698864075849517020699033700786598720604069513063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15841069595399679087/4000000000000000000)
  centralHi := (49503342485623997147/12500000000000000000)
  directionLo := (399157434768515471931/100000000000000000000)
  directionHi := (99789358692128867983/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree065.table
  base := (247221117023436718279588664533925147491/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2072295446213637361429126183983095525000000000000)
      constant := (38088527382658254653850740589707914444253617956380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree065.table
  base := (4944390958044960149224702660466343064001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-18655201536266951144267162059217865975000000000000)
      constant := (342962974557964851288007360932423511170220602013681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399157434768515471931/100000000000000000000)
  centralHi := (99789358692128867983/25000000000000000000)
  directionLo := (100565941289169898857/25000000000000000000)
  directionHi := (402263765156679595429/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree066.table
  base := (21168528334966166664412827468674540143229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-8409760308469479457485948161920543900000000000000)
      constant := (156878795515824920945549667043003523472713237086661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree066.table
  base := (4233682896320897019009050348020472621497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-8411810266368407203350780590108033900000000000000)
      constant := (156954903396406588278199698507599865236251900251365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100565941289169898857/25000000000000000000)
  centralHi := (402263765156679595429/100000000000000000000)
  directionLo := (202673145597212053133/50000000000000000000)
  directionHi := (405346291194424106267/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree067.table
  base := (22580933842758217948737563675406562747661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-8530338832084409469255391587908705700000000000000)
      constant := (161468910020379417052786694531406336278702670747349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree067.table
  base := (22580830601390230650406959295023695813123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-76791778649563525083245402385073146300000000000000)
      constant := (1453925516660585006851735371216239256278651515503763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202673145597212053133/50000000000000000000)
  centralHi := (405346291194424106267/100000000000000000000)
  directionLo := (102101387971748898553/25000000000000000000)
  directionHi := (408405551886995594213/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree068.table
  base := (12007414715162623624382386341345685822253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-4325458677849669740512417506948433750000000000000)
      constant := (83062224315872823353992711896874835846931010943477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree068.table
  base := (24014735831021109443050409349090151056843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-77877264901811385336333779459173987500000000000000)
      constant := (1495846016846718092035729361882744997903697772357083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102101387971748898553/25000000000000000000)
  centralHi := (408405551886995594213/100000000000000000000)
  directionLo := (642878228437961139/156250000000000000)
  directionHi := (411442066200295128961/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree069.table
  base := (25470146827995098838954549065708146764893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-8771495879314269492794278439885029300000000000000)
      constant := (170845407409779828819690352982524102157021061443237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree069.table
  base := (1273503099358970426846807481181555110897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737501566)
      previous := (0)
      next := (647644250)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2193409754279423488595059903702078575000000000000)
      constant := (42732099880822766136215630901871983480881749074365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642878228437961139/156250000000000000)
  centralHi := (411442066200295128961/100000000000000000000)
  directionLo := (414456334088664433567/100000000000000000000)
  directionHi := (12951760440270763549/3125000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree070.table
  base := (6736706268155517844847778433959894143947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2223018600732299876140930466468297775000000000000)
      constant := (43907945709007509613544433699463880226470462032323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree070.table
  base := (26946748185665636711763297422592837436897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-80048237406307105842510533607375669900000000000000)
      constant := (1581454221624229153790912234747348878992732266339857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414456334088664433567/100000000000000000000)
  centralHi := (12951760440270763549/3125000000000000000)
  directionLo := (208724418727937302769/50000000000000000000)
  directionHi := (417448837455874605539/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree071.table
  base := (5688961944715766859271749044910803538367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8128790000000000000000000000000000000000000000
      center := (41538684)
      previous := (0)
      next := (36497700)
      square := (1595239964983773145724144116810400000000000000)
      linear := (-126938773613297598821593877350159900000000000000)
      constant := (2542022137584333008987858245650408620347321142965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree071.table
  base := (28444740057990907144739205067955500501081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73159110000000000000000000000000000000000000000
      center := (373944456)
      previous := (0)
      next := (328383000)
      square := (14357159684853958311517297051293600000000000000)
      linear := (-1142728502233168536557731136358824100000000000000)
      constant := (22889322061266760165672811833944763018626363999791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208724418727937302769/50000000000000000000)
  centralHi := (417448837455874605539/100000000000000000000)
  directionLo := (84084008210909595249/20000000000000000000)
  directionHi := (210210020527273988123/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree072.table
  base := (29964052163196871078510590981678098502567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9133231450159059528102608717849514700000000000000)
      constant := (185400771401212638983211829523551176583319439387903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree072.table
  base := (7490997263093437284753050813027798514613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737501566)
      previous := (0)
      next := (647644250)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2283866941966745176352424659877148675000000000000)
      constant := (46372736240764324264265511626744750841841967158717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84084008210909595249/20000000000000000000)
  centralHi := (210210020527273988123/50000000000000000000)
  directionLo := (105842598332191607553/25000000000000000000)
  directionHi := (423370393328766430213/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree073.table
  base := (6300901794501614263382913268655121052659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9253809973773989539872052143837676500000000000000)
      constant := (190383379228304940607301153457454972331888360317655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree073.table
  base := (1969028238124785924246504525809928858601/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-10413087020381335825221958103709774187500000000000)
      constant := (214285514256887433852468002704499666942936623072562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105842598332191607553/25000000000000000000)
  centralHi := (423370393328766430213/100000000000000000000)
  directionLo := (426300327204191790837/100000000000000000000)
  directionHi := (213150163602095895419/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree074.table
  base := (33066141374138993477378343139114593307121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9374388497388919551641495569825838300000000000000)
      constant := (195431393011751357759963943730211411210995844006489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree074.table
  base := (16533044804187935423357677263528808736703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-42195091207649273427432020951889517350000000000000)
      constant := (879869337199542052434405301722964150031415652281743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426300327204191790837/100000000000000000000)
  centralHi := (213150163602095895419/50000000000000000000)
  directionLo := (429210260829639966641/100000000000000000000)
  directionHi := (214605130414819983321/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree075.table
  base := (17324457367548937040114472227399149918401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-4747483510501924781705469497907000050000000000000)
      constant := (100272405376364619455051545482967720232142911940009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree075.table
  base := (34648867864588666191676767835396399129631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9497296518616267456439157664208875100000000000000)
      constant := (200642463081785880969158756223626854331494767553079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429210260829639966641/100000000000000000000)
  centralHi := (214605130414819983321/50000000000000000000)
  directionLo := (432100598273705426583/100000000000000000000)
  directionHi := (54012574784213178323/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree076.table
  base := (36252798122985052999696253283073800160579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9615545544618779575180382421802161900000000000000)
      constant := (205723630665993418721758907191692608829651922082811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree076.table
  base := (36252755691888332409603199725506684216699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-86561154919794267361040796051980717100000000000000)
      constant := (1852414578022572994056091572910653901046047696443019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432100598273705426583/100000000000000000000)
  centralHi := (54012574784213178323/12500000000000000000)
  directionLo := (434971730179721852109/100000000000000000000)
  directionHi := (43497173017972185211/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree077.table
  base := (18938881954930542503866015364933623060023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-4868062034116854793474912923895161850000000000000)
      constant := (105483925578506850112903359038110315279137998971407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree077.table
  base := (37877725503946279023196443121875167406283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-87646641172042127614129173126081558300000000000000)
      constant := (1899635890929426441156996258696859117152667176085723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434971730179721852109/100000000000000000000)
  centralHi := (43497173017972185211/10000000000000000000)
  directionLo := (8756480687641293227/2000000000000000000)
  directionHi := (437824034382064661351/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree078.table
  base := (19761893709316563632523739115417502189703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-4928351295924319799359634636889242750000000000000)
      constant := (108138735400783127079823544315029182189634914530527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree078.table
  base := (39523752661582321480518809943998423375147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-9859125269365554207468616688909155500000000000000)
      constant := (216382899295367974073534304679969326752028394393123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8756480687641293227/2000000000000000000)
  centralHi := (437824034382064661351/100000000000000000000)
  directionLo := (110164469121637038233/25000000000000000000)
  directionHi := (440657876486548152933/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree079.table
  base := (20595423303688918939415106615179865156389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-4988640557731784805244356349883323650000000000000)
      constant := (110826244163757250811315705423063222808700683709101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree079.table
  base := (41190815157404038496091195111554252641213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-89817613676537848120305927274283240700000000000000)
      constant := (1995845174777936145540395001695211132438618676043053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110164469121637038233/25000000000000000000)
  centralHi := (440657876486548152933/100000000000000000000)
  directionLo := (88694722083488263521/20000000000000000000)
  directionHi := (221736805208720658803/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree080.table
  base := (21439460893757810864504399713791781333571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-5048929819539249811129078062877404550000000000000)
      constant := (113546451299271853616472738870269858308724282124539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree080.table
  base := (42878893334271927495152340962599092652029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-90903099928785708373394304348384081900000000000000)
      constant := (2044833124077797876597848118704818541627132867472749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88694722083488263521/20000000000000000000)
  centralHi := (221736805208720658803/50000000000000000000)
  directionLo := (223135789466709656939/50000000000000000000)
  directionHi := (446271578933419313879/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree081.table
  base := (2786749710762086447673618673046697416623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2554609540673357408506899887935742725000000000000)
      constant := (58149678149909759601291790008870061670708892883228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree081.table
  base := (44587969633949381071706788024538065714181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10220954020114840958498075713609435900000000000000)
      constant := (232712214715291968880749959349694198085697119334029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223135789466709656939/50000000000000000000)
  centralHi := (446271578933419313879/100000000000000000000)
  directionLo := (224526057057289952961/50000000000000000000)
  directionHi := (449052114114579905923/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree082.table
  base := (46318051651626994365872807222627167209223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10339016686308359645797042977731132700000000000000)
      constant := (238169917424119588684915708568226062557824484794207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree082.table
  base := (23159014186345224164998039441115869384763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-46537036216640714439785529248292882150000000000000)
      constant := (1072287795855411259684137034117150447793565111350603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224526057057289952961/50000000000000000000)
  centralHi := (449052114114579905923/100000000000000000000)
  directionLo := (3614524302579870343/800000000000000000)
  directionHi := (112953884455620948219/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree083.table
  base := (48069076592505791656527503384482301628639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10459595209923289657566486403719294500000000000000)
      constant := (243806516262061126804400233337121171084456637359351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree083.table
  base := (24034527770434671092742815796395354525117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-47079779342764644566329717785343302750000000000000)
      constant := (1097665047310183410703863851516957238688363429797677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3614524302579870343/800000000000000000)
  centralHi := (112953884455620948219/25000000000000000000)
  directionLo := (454562162135022927377/100000000000000000000)
  directionHi := (227281081067511463689/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree084.table
  base := (49841057658874300563133510972105195989637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10580173733538219669335929829707456300000000000000)
      constant := (249508508389958391304177263854147456922371069579533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree084.table
  base := (9968207724813687780148674912154723704699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10582782770864127709527534738309716300000000000000)
      constant := (249630381629544519094044241093122140275874966539455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454562162135022927377/100000000000000000000)
  centralHi := (227281081067511463689/50000000000000000000)
  directionLo := (457292289757780040803/100000000000000000000)
  directionHi := (114323072439445010201/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree085.table
  base := (51633983652185266249607970926769424048483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10700752257153149681105373255695618100000000000000)
      constant := (255275893161493845712809886033700228088228583691547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree085.table
  base := (25816983221660145917928574350401135386943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-48165265595012504819418094859444143950000000000000)
      constant := (1149302803020368287983365686992558001288577614055183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457292289757780040803/100000000000000000000)
  centralHi := (114323072439445010201/25000000000000000000)
  directionLo := (460006214413414255587/100000000000000000000)
  directionHi := (115001553603353563897/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree086.table
  base := (10689568913693332377936256863992151157697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10821330780768079692874816681683779900000000000000)
      constant := (261108669999294156849487804298953252548525740780365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree086.table
  base := (53447829012447681289040854574659505354437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-97416017442272869891924566792989129100000000000000)
      constant := (2351126603557757686129561646713537278799873002844597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460006214413414255587/100000000000000000000)
  centralHi := (115001553603353563897/25000000000000000000)
  directionLo := (231352110605245310153/50000000000000000000)
  directionHi := (462704221210490620307/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree087.table
  base := (55282631470766981845029447525837158025321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10941909304383009704644260107671941700000000000000)
      constant := (267006838387568450304634981030127200230671008550289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree087.table
  base := (55282617410667264580175640314600085767879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-10944611521613414460556993763009996700000000000000)
      constant := (267137380287027150708493463083957103196442447668511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231352110605245310153/50000000000000000000)
  centralHi := (462704221210490620307/100000000000000000000)
  directionLo := (232693293496532268909/50000000000000000000)
  directionHi := (465386586993064537819/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree088.table
  base := (57138336375240748572448813523425710166707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-11062487827997939716413703533660103500000000000000)
      constant := (272970397865533802794522645772762008417676785981163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree088.table
  base := (28569161834409962492868139696663965868171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-49793494973384295199050660470595405750000000000000)
      constant := (1228967529488889404434713731750409905855098950583451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232693293496532268909/50000000000000000000)
  centralHi := (465386586993064537819/100000000000000000000)
  directionLo := (468053580672234378823/100000000000000000000)
  directionHi := (58506697584029297353/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree089.table
  base := (59014952149412395002260507562278392570767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-11183066351612869728183146959648265300000000000000)
      constant := (278999348021543602258784420450850547170691808081703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree089.table
  base := (7376867583470883475754981263481871215809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (127419792203078880014716011330230700000000000000)
      linear := (-12584059524877056331398712251911456587500000000000)
      constant := (314027813630433644296109492890977981980535751026929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468053580672234378823/100000000000000000000)
  centralHi := (58506697584029297353/12500000000000000000)
  directionLo := (235352731770393098873/50000000000000000000)
  directionHi := (470705463540786197747/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree090.table
  base := (60912472421313860752364983160280933469587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-11303644875227799739952590385636427100000000000000)
      constant := (285093688487843477925591115560009562224165533179083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree090.table
  base := (15228115511912302457282137935097570104831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737501566)
      previous := (0)
      next := (647644250)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-2826610068090675302896613196927569275000000000000)
      constant := (71308299152133766952921514189564509803436389209879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235352731770393098873/50000000000000000000)
  centralHi := (470705463540786197747/100000000000000000000)
  directionLo := (47334248957197260393/10000000000000000000)
  directionHi := (473342489571972603931/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree091.table
  base := (1256617829966628734294361816605643007041/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-5712111699421364875861016905812294450000000000000)
      constant := (145626709467943796954237022933340234992908853844225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree091.table
  base := (62830882126843330472218447722993000310967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-102843448703512171157366452163493335100000000000000)
      constant := (2622563837326614543534751272326905545391758489611527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47334248957197260393/10000000000000000000)
  centralHi := (473342489571972603931/100000000000000000000)
  directionLo := (237982452851696390627/50000000000000000000)
  directionHi := (95192981140678556251/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree092.table
  base := (64770204294722455525350978613664317422303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-11544801922457659763491477237612750700000000000000)
      constant := (297478539072155317834438161185663155954416621063927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree092.table
  base := (64770195829580446114847968330158320744017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-103928934955760031410454829237594176300000000000000)
      constant := (2678617709956360890065935649400295212923560432968577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237982452851696390627/50000000000000000000)
  centralHi := (95192981140678556251/20000000000000000000)
  directionLo := (119643238026717939889/25000000000000000000)
  directionHi := (478572952106871759557/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree093.table
  base := (33365203133436999744412130896427301015501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-5832690223036294887630460331800456250000000000000)
      constant := (151884524317207357716962767716329636089574740053909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree093.table
  base := (6673039862129637776660574899332869581337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1475003132)
      previous := (0)
      next := (1295288500)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-5834134511555993981307955906205278750000000000000)
      constant := (151958910278370412496206186938215044823304711924165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119643238026717939889/25000000000000000000)
  centralHi := (478572952106871759557/100000000000000000000)
  directionLo := (120291715611293438247/25000000000000000000)
  directionHi := (481166862445173752989/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree094.table
  base := (34355746677737673301916448167679619157399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-5892979484843759893515182044794537150000000000000)
      constant := (155062473694192533719633775381307232083514361262191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree094.table
  base := (34355743225444085017670976644897735285837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (13275028188)
      previous := (0)
      next := (11657596500)
      square := (509679168812315520058864045320922800000000000000)
      linear := (-53049953730127875958315791692897929350000000000000)
      constant := (1396245930192635516157288399676191294642144756727997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120291715611293438247/25000000000000000000)
  centralHi := (481166862445173752989/100000000000000000000)
  directionLo := (483746864116326183087/100000000000000000000)
  directionHi := (30234179007270386443/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree095.table
  base := (70713461933864703053533111734974238892399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-11906537493302449798799807515577236100000000000000)
      constant := (316546235124755731777445214715431537952899622877191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree095.table
  base := (17678363924784347462932978826135530208177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-26796348428125903042429990114974174975000000000000)
      constant := (712578033550060559014003197673040488512549242701537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483746864116326183087/100000000000000000000)
  centralHi := (30234179007270386443/6250000000000000000)
  directionLo := (486313178486277438621/100000000000000000000)
  directionHi := (243156589243138719311/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree096.table
  base := (1818407719047250949475513699571901366941/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (737311641)
      previous := (0)
      next := (647834175)
      square := (28315509378461973336603558073384600000000000000)
      linear := (-3006779004229344952642312735391349475000000000000)
      constant := (80758227914130812229321774941419501903992919528690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree096.table
  base := (72736303132640747493068210593506526245701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2950006264)
      previous := (0)
      next := (2590577000)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-12030097773861274713645370837110837900000000000000)
      constant := (323191244975117266314555871441322012399913622005709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486313178486277438621/100000000000000000000)
  centralHi := (243156589243138719311/50000000000000000000)
  directionLo := (488866021110562076853/100000000000000000000)
  directionHi := (244433010555281038427/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree097.table
  base := (74780030944694577887662064171233207116199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (2949246564)
      previous := (0)
      next := (2591336700)
      square := (113262037513847893346414232293538400000000000000)
      linear := (-12147694540532309822338694367553559700000000000000)
      constant := (329584976816612671037019018332044655899886019611391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree097.table
  base := (18695006465664793574251546264920041570201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (6637514094)
      previous := (0)
      next := (5828798250)
      square := (254839584406157760029432022660461400000000000000)
      linear := (-27339091554249833168974178652024595575000000000000)
      constant := (741929767653053425428007043950481645764566244535881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell170.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488866021110562076853/100000000000000000000)
  centralHi := (244433010555281038427/50000000000000000000)
  directionLo := (245702800972800834591/50000000000000000000)
  directionHi := (491405601945601669183/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree098.table
  base := (38422312947950327620225916831550884104739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1474623282)
      previous := (0)
      next := (1295668350)
      square := (56631018756923946673207116146769200000000000000)
      linear := (-6134136532073619917054068896770860750000000000000)
      constant := (168101215227876369801914382341311903217032505484251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree098.table
  base := (76844621308359582463053491243155812262561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (26550056376)
      previous := (0)
      next := (23315193000)
      square := (1019358337624631040117728090641845600000000000000)
      linear := (-110441852469247192928985091682199223500000000000000)
      constant := (3027305730368155843188634057498206596346837948473041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell170.Kernel098
