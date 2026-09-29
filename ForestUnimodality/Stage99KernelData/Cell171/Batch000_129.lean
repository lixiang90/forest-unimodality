import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell171.Parameters
import ForestUnimodality.BinomialMassData.Q7_12.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_12.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_12.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_90.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_90.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_90.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree000.table
  base := (159977602905575925673531399/10000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-7662249437690178410775843200000000000000)
      constant := (639910411622303702694125596000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree000.table
  base := (159977602905575925673531399/10000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-57466870782676338080818824000000000000000)
      constant := (4799328087167277770205941970000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree001.table
  base := (12585849271057435041747772565889023919753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-94451503809274895279157747720000000000000)
      constant := (3672386350116183188141399430461038888888864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree001.table
  base := (50059582678536420398262648482167206790123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-2130621248323698705834372572040000000000000)
      constant := (82180735151735478107423676560344874999999260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49203532945521174783/100000000000000000000)
  directionHi := (192201300568442089/390625000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree002.table
  base := (1284310432014983722057381850998949845679/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-119942762679338184861332906640000000000000)
      constant := (2421952198737791410862304704138109722222200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree002.table
  base := (12703423375706957269099456370235887345679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-2709636985515136283486636896080000000000000)
      constant := (53958263030749977637835503773191343749999950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49203532945521174783/100000000000000000000)
  centralHi := (192201300568442089/390625000000000000)
  directionLo := (69584303608227447063/100000000000000000000)
  directionHi := (8698037951028430883/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree003.table
  base := (20770467940572804060329294221379066257363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-16159335727711274938167562840000000000000)
      constant := (187007630544308704162959834056032530058904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree003.table
  base := (20443954211654561988314283002272588912541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-365405858078508206793211246680000000000000)
      constant := (4154974140307929036478077425243066004257380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/100000000000000000000)
  centralHi := (8698037951028430883/12500000000000000000)
  directionLo := (42611509486765905237/50000000000000000000)
  directionHi := (3408920758941272419/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree004.table
  base := (27229185795787590878137034182533903954349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-170925280419464764025683224480000000000000)
      constant := (1260117134900142369622710012731220542356564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree004.table
  base := (6669097885532968910227234303754861821501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-3867668459898011438791165544160000000000000)
      constant := (27990577603895806959126983832709752301663240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/50000000000000000000)
  centralHi := (3408920758941272419/4000000000000000000)
  directionLo := (98407065891042349567/100000000000000000000)
  directionHi := (192201300568442089/195312500000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree005.table
  base := (22506444420595048279948731425208138181/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-196416539289528053607858383400000000000000)
      constant := (1035193409646716060282083216170994379612800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree005.table
  base := (43888559313551660645372343476684989763/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-4446684197089449016443429868200000000000000)
      constant := (23050708621361589095354903735295936683212000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98407065891042349567/100000000000000000000)
  centralHi := (192201300568442089/195312500000000000)
  directionLo := (55011222199667901651/50000000000000000000)
  directionHi := (110022444399335803303/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree006.table
  base := (5949595682143384725381879411838905051407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-24656422017732371465559282480000000000000)
      constant := (104154440504136540086641505234711240411256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree006.table
  base := (11536416777103324417602186644487179960461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-558411103808987399343966021360000000000000)
      constant := (2329378208483361528253543202939846196441490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55011222199667901651/50000000000000000000)
  centralHi := (110022444399335803303/100000000000000000000)
  directionLo := (120523549258748291833/100000000000000000000)
  directionHi := (60261774629374145917/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree007.table
  base := (7720679297720736916418118337208434896499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-247399057029654632772208701240000000000000)
      constant := (923844696237715099198984477304503656273964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree007.table
  base := (7424677751404296893805584735767703462519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-5604715671472324171747958516280000000000000)
      constant := (20763962082783597963282827911237839804640390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120523549258748291833/100000000000000000000)
  centralHi := (60261774629374145917/50000000000000000000)
  directionLo := (13018031179962242501/10000000000000000000)
  directionHi := (130180311799622425011/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree008.table
  base := (949594158102715837731700727184025775093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-272890315899717922354383860160000000000000)
      constant := (968578257082657749578227845133124639516740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree008.table
  base := (4500435793691345837428425424563816219887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-6183731408663761749400222840320000000000000)
      constant := (21866368848409510684399848935272691138108470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13018031179962242501/10000000000000000000)
  centralHi := (130180311799622425011/100000000000000000000)
  directionLo := (69584303608227447063/50000000000000000000)
  directionHi := (139168607216454894127/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree009.table
  base := (1271045778937498536406834173868132285337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-33153508307753467992951002120000000000000)
      constant := (117309730313289560101037642355945058282696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree009.table
  base := (1164208174709077428028235882262103704533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-250472116513155530631573598680000000000000)
      constant := (885890806816499097769534073037726222271980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/50000000000000000000)
  centralHi := (139168607216454894127/100000000000000000000)
  directionLo := (147610598836563524351/100000000000000000000)
  directionHi := (576603901705326267/390625000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree010.table
  base := (104344875167881480606698429286809937423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-323872833639844501518734178000000000000000)
      constant := (1175814469903930179127236384134601261977824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree010.table
  base := (644089259297224027357032940479161076739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-7341762883046636904704751488400000000000000)
      constant := (26707741460668617892326061461188120472158590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147610598836563524351/100000000000000000000)
  centralHi := (576603901705326267/390625000000000000)
  directionLo := (31119046606996093217/20000000000000000000)
  directionHi := (77797616517490233043/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree011.table
  base := (-269505985331497130857729618718509062823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-349364092509907791100909336920000000000000)
      constant := (1322719485038723604638146729137267347476744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree011.table
  base := (-714366069036146844356031594944255850063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-7920778620238074482357015812440000000000000)
      constant := (30101363198463530283539999559409152761448970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31119046606996093217/20000000000000000000)
  centralHi := (77797616517490233043/50000000000000000000)
  directionLo := (81594828570092087971/50000000000000000000)
  directionHi := (163189657140184175943/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree012.table
  base := (-840764280264844375575293846072165238081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-41650594597774564520342721760000000000000)
      constant := (165868839882007845254312626591422678095352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree012.table
  base := (-230851880678281385416262841195421421161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-944421595269945784445475570720000000000000)
      constant := (3779891779495148357864317305283296576764080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81594828570092087971/50000000000000000000)
  centralHi := (163189657140184175943/100000000000000000000)
  directionLo := (42611509486765905237/25000000000000000000)
  directionHi := (170446037947063620949/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree013.table
  base := (-2656944552562703176786776659910922075137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-400346610250034370265259654760000000000000)
      constant := (1683805155366967011159177880408206805295068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree013.table
  base := (-175976551229857672272762235989877146301/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-9078810094620949637661544460520000000000000)
      constant := (38410212520305279109935427622517192183939040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/25000000000000000000)
  centralHi := (170446037947063620949/100000000000000000000)
  directionLo := (177405860969058289751/100000000000000000000)
  directionHi := (22175732621132286219/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree014.table
  base := (-3506096795006933409876384664158551339343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-425837869120097659847434813680000000000000)
      constant := (1894206147788596564884154545550292151783652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree014.table
  base := (-1830185868673125693415996376889888197333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-9657825831812387215313808784560000000000000)
      constant := (43242865873110253437077032748102381120320540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177405860969058289751/100000000000000000000)
  centralHi := (22175732621132286219/12500000000000000000)
  directionLo := (11506422656311518107/6250000000000000000)
  directionHi := (184102762500984289713/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree015.table
  base := (-4255501530492484944101765778050646066309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-50147680887795661047734441400000000000000)
      constant := (235896439052030607854575432012797415734764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree015.table
  base := (-4406707303080948229416825132484673284633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-1137426841000424976996230345400000000000000)
      constant := (5388467595011719787323352514926379404383030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11506422656311518107/6250000000000000000)
  centralHi := (184102762500984289713/100000000000000000000)
  directionLo := (190564463672571478771/100000000000000000000)
  directionHi := (47641115918142869693/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree016.table
  base := (-4922824118945589664592855695483890678097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-476820386860224239011785131520000000000000)
      constant := (2369754613448659380715573223122579935588508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree016.table
  base := (-5071717878684487734132925063528872736573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-10815857306195262370618337432640000000000000)
      constant := (54156400013230786751923319238445613083375870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190564463672571478771/100000000000000000000)
  centralHi := (47641115918142869693/25000000000000000000)
  directionLo := (39362826356416939827/20000000000000000000)
  directionHi := (192201300568442089/97656250000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree017.table
  base := (-2760107528839990466880866643207047774513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-502311645730287528593960290440000000000000)
      constant := (2633828715826453893910502711254092560235064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree017.table
  base := (-1416793876116484036882068060282846180541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-11394873043386699948270601756680000000000000)
      constant := (60213905494835835775412609008109578375047160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39362826356416939827/20000000000000000000)
  centralHi := (192201300568442089/97656250000000000)
  directionLo := (1267946021799639097/625000000000000000)
  directionHi := (202871363487942255521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree018.table
  base := (-1211270438840397795772092582268393968277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-58644767177816757575126161040000000000000)
      constant := (323886428454603458010543670614632120634460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree018.table
  base := (-775189671159705615745786218555987747989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-443477362243634723182328373360000000000000)
      constant := (2468958913961119276915691453554562940482640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1267946021799639097/625000000000000000)
  centralHi := (202871363487942255521/100000000000000000000)
  directionLo := (208752910824682341189/100000000000000000000)
  directionHi := (20875291082468234119/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree019.table
  base := (-1634424110974592797050913938493810076187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-553294163470414107758310608280000000000000)
      constant := (3212969441289667799289418193341891349029072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree019.table
  base := (-6681056807386998640450744496816249268121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-12552904517769575103575130404760000000000000)
      constant := (73495241758817359353343448753852838092821990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208752910824682341189/100000000000000000000)
  centralHi := (20875291082468234119/10000000000000000000)
  directionLo := (214473227774700974289/100000000000000000000)
  directionHi := (21447322777470097429/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree020.table
  base := (-1393853606668275226381216427108329452623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-578785422340477397340485767200000000000000)
      constant := (3527622743264562976969946453120500698527860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree020.table
  base := (-3555364191965357305559270347252836857523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-13131920254961012681227394728800000000000000)
      constant := (80709961742676511375961055123050404290812740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214473227774700974289/100000000000000000000)
  centralHi := (21447322777470097429/10000000000000000000)
  directionLo := (44008977759734321321/20000000000000000000)
  directionHi := (110022444399335803303/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree021.table
  base := (-367756474126371326467930039233159444951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-67141853467837854102517880680000000000000)
      constant := (428754612366249493026489655626347244403920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree021.table
  base := (-3747274764351363213360708589689442271497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-1523437332461383362097739894760000000000000)
      constant := (9811421834488287815298619988321900391130540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44008977759734321321/20000000000000000000)
  centralHi := (110022444399335803303/50000000000000000000)
  directionLo := (225478914182104266981/100000000000000000000)
  directionHi := (112739457091052133491/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree022.table
  base := (-3849344273375299522641682318501880501649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-629767940080603976504836085040000000000000)
      constant := (4206353066194128420164802030207864603881272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree022.table
  base := (-7835909037597727508849709526545774154337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-14289951729343887836531923376880000000000000)
      constant := (96271001137296894567034851253553922934987030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225478914182104266981/100000000000000000000)
  centralHi := (112739457091052133491/50000000000000000000)
  directionLo := (23078502636666384989/10000000000000000000)
  directionHi := (230785026366663849891/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree023.table
  base := (-8002890149899385962219803274940304545151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-655259198950667266087011243960000000000000)
      constant := (4570201390698226203577712376867149036374564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree023.table
  base := (-63576166716217991038817704138234831183/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-14868967466535325414184187700920000000000000)
      constant := (104612192255844674217676018000133812702946560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23078502636666384989/10000000000000000000)
  centralHi := (230785026366663849891/100000000000000000000)
  directionLo := (5899296358962159949/2500000000000000000)
  directionHi := (235971854358486397961/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree024.table
  base := (-4135169765292258824915403547857290887601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-75638939757858950629909600320000000000000)
      constant := (550026966246505832685474876257141672899192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree024.table
  base := (-8402683231650535593295582290278028746093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-1716442578191862554648494669440000000000000)
      constant := (12591583722300018883432785660050977412851630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5899296358962159949/2500000000000000000)
  centralHi := (235971854358486397961/100000000000000000000)
  directionLo := (241047098517496583667/100000000000000000000)
  directionHi := (60261774629374145917/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree025.table
  base := (-4251691257901825559670000763243749695181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-706241716690793845251361561800000000000000)
      constant := (5346392532983191639535436043171450021946968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree025.table
  base := (-67445858875202327419956023152407263917/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-16026998940918200569488716349000000000000000)
      constant := (122405273901634921300953640580808414877085440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241047098517496583667/100000000000000000000)
  centralHi := (60261774629374145917/25000000000000000000)
  directionLo := (246017664727605873919/100000000000000000000)
  directionHi := (192201300568442089/78125000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree026.table
  base := (-1088019861398721764369292190254927308817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-731732975560857134833536720720000000000000)
      constant := (5758573868709356080884748613066580935060704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree026.table
  base := (-1103883215777843277225242629450629437791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-16606014678109638147140980673040000000000000)
      constant := (131853506877178115571331630723343921243114320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246017664727605873919/100000000000000000000)
  centralHi := (192201300568442089/78125000000000000)
  directionLo := (250889774626917944091/100000000000000000000)
  directionHi := (62722443656729486023/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree027.table
  base := (-887463875205325305541904064990808089923/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-84136026047880047157301319960000000000000)
      constant := (687412864440652514126931497285367676403080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree027.table
  base := (-8998658511042722983003489704330522689029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-636482607974113915733083148040000000000000)
      constant := (5246938600785200828330415986588084319329130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250889774626917944091/100000000000000000000)
  centralHi := (62722443656729486023/25000000000000000000)
  directionLo := (127834528460297715711/50000000000000000000)
  directionHi := (255669056920595431423/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree028.table
  base := (-4508323991877192052000677787693645200027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-782715493300983713997887038560000000000000)
      constant := (6630752534879770616430719822726057545598056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree028.table
  base := (-2284423049111845878725721414385306356911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-17764046152492513302445509321120000000000000)
      constant := (151845286369872981880991909687247607403608360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127834528460297715711/50000000000000000000)
  centralHi := (255669056920595431423/100000000000000000000)
  directionLo := (13018031179962242501/5000000000000000000)
  directionHi := (260360623599244850021/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree029.table
  base := (-4565943358819999337773099029047506690207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-808206752171047003580062197480000000000000)
      constant := (7090622928722564117815340687193579518305096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree029.table
  base := (-2312471112521984211258132327527402416727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-18343061889683950880097773645160000000000000)
      constant := (162385948012398314804002420535405216169804520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13018031179962242501/5000000000000000000)
  centralHi := (260360623599244850021/100000000000000000000)
  directionLo := (66242283501225938063/25000000000000000000)
  directionHi := (264969134004903752253/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree030.table
  base := (-2305485795947357571911298154982424054741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-92633112337901143684693039600000000000000)
      constant := (840696642801266347184771954020281215124144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree030.table
  base := (-4668420071498352175980827140769350957521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-2102453069652820939750004218800000000000000)
      constant := (19254225244804471201923520550061516827646220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66242283501225938063/25000000000000000000)
  centralHi := (264969134004903752253/100000000000000000000)
  directionLo := (269498849032105570567/100000000000000000000)
  directionHi := (33687356129013196321/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree031.table
  base := (-4644152247832006233950324869222980119747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-859189269911173582744412515320000000000000)
      constant := (8057639568261661629979857342500945431378216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree031.table
  base := (-9400061906185075611611276580351122851351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-19501093364066826035402302293240000000000000)
      constant := (184550306811279534364423679965789590490405690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269498849032105570567/100000000000000000000)
  centralHi := (33687356129013196321/12500000000000000000)
  directionLo := (68488419314851423867/25000000000000000000)
  directionHi := (273953677259405695469/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree032.table
  base := (-9332365347823414580623880109531026270617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-884680528781236872326587674240000000000000)
      constant := (8564682068869209536650862771096883054257788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree032.table
  base := (-59005991993144874526630009748697634157/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-20080109101258263613054566617280000000000000)
      constant := (196171645563323590712112087244984786613252800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68488419314851423867/25000000000000000000)
  centralHi := (273953677259405695469/100000000000000000000)
  directionLo := (69584303608227447063/25000000000000000000)
  directionHi := (278337214432909788253/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree033.table
  base := (-9355435259640171720499782430273899309189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-101130198627922240212084759240000000000000)
      constant := (1009705571592958842363034168763904402763244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree033.table
  base := (-29565165996685572513138145327435229799/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-2295458315383300132300758993480000000000000)
      constant := (23127885800418203718866531687483865381788800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/25000000000000000000)
  centralHi := (278337214432909788253/100000000000000000000)
  directionLo := (70663194359136051139/25000000000000000000)
  directionHi := (282652777436544204557/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree034.table
  base := (-9358744777665156936120944583549568071743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-935663046521363451490937992080000000000000)
      constant := (9625599494988090334079858422052215549417252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree034.table
  base := (-473049370976489423093752891115965806227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-21238140575641138768359095265360000000000000)
      constant := (220487280458879019199032585003225353939122600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70663194359136051139/25000000000000000000)
  centralHi := (282652777436544204557/100000000000000000000)
  directionLo := (28690343366176986249/10000000000000000000)
  directionHi := (286903433661769862491/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree035.table
  base := (-467172545450675549872505957793939364717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-961154305391426741073113151000000000000000)
      constant := (10179388468567446727369856387513363657403760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree035.table
  base := (-472126459336890205150557351233175107261/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-21817156312832576346011359589400000000000000)
      constant := (233179624600157787091165875567672563262371800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28690343366176986249/10000000000000000000)
  centralHi := (286903433661769862491/100000000000000000000)
  directionLo := (291092026516073723769/100000000000000000000)
  directionHi := (29109202651607372377/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree036.table
  base := (-9310641968143844803504681939008738142963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-109627284917943336739476478880000000000000)
      constant := (1194297542861576529863630654083965047428148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree036.table
  base := (-9406576147500546169223504454326642492881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-829487853704593108283837922720000000000000)
      constant := (9119522795140039746388656381602200725213570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291092026516073723769/100000000000000000000)
  centralHi := (29109202651607372377/10000000000000000000)
  directionLo := (295221197673127048703/100000000000000000000)
  directionHi := (576603901705326267/195312500000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree037.table
  base := (-926134196120404507801888362655916388287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1012136823131553320237463468840000000000000)
      constant := (11333430882326992536233883894808870100216680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree037.table
  base := (-187083212890650591058605733678317244781/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-22975187787215451501315888237480000000000000)
      constant := (259628916867150120320157418386174151586369500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295221197673127048703/100000000000000000000)
  centralHi := (576603901705326267/195312500000000000)
  directionLo := (299293406559310195589/100000000000000000000)
  directionHi := (29929340655931019559/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree038.table
  base := (-2299128648537494477709629559001947875921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1037628082001616609819638627760000000000000)
      constant := (11933612764871446850519031827043719505867376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree038.table
  base := (-4643126859544806828731415653193578086261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-23554203524406889078968152561520000000000000)
      constant := (273384242251847682477458580366122403500257180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299293406559310195589/100000000000000000000)
  centralHi := (29929340655931019559/10000000000000000000)
  directionLo := (151655473742458048859/50000000000000000000)
  directionHi := (303310947484916097719/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree039.table
  base := (-2279266741459003770205790436913308123277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-118124371207964433266868198520000000000000)
      constant := (1394354541980977147509908327574387070027568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree039.table
  base := (-1840753775886777671789895804945640915841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-2681468806844258517402268542840000000000000)
      constant := (31943594631242385202748139141520461587871550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151655473742458048859/50000000000000000000)
  centralHi := (303310947484916097719/100000000000000000000)
  directionLo := (153637982379454689419/50000000000000000000)
  directionHi := (307275964758909378839/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree040.table
  base := (-9023852990628474096867192086521590722733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1088610599741743188983988945600000000000000)
      constant := (13180134480281847537124115652885222733981612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree040.table
  base := (-9107565597418716749021539244915874141819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-24712234998789764234272681209600000000000000)
      constant := (301952548982950249257760073490018141945126610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153637982379454689419/50000000000000000000)
  centralHi := (307275964758909378839/100000000000000000000)
  directionLo := (31119046606996093217/10000000000000000000)
  directionHi := (311190466069960932171/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree041.table
  base := (-8917676583877303799026139130784535979239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1114101858611806478566164104520000000000000)
      constant := (13826414631278008320881854865576756704747396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree041.table
  base := (-4499226282606563251201643186761824524359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-25291250735981201811924945533640000000000000)
      constant := (316764179116497117360012381745799844270538420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31119046606996093217/10000000000000000000)
  centralHi := (311190466069960932171/100000000000000000000)
  directionLo := (315056334370792319461/100000000000000000000)
  directionHi := (157528167185396159731/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree042.table
  base := (-8799294635922705571408880360905551593459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-126621457497985529794259918160000000000000)
      constant := (1609778231418336603226052555216377793626164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree042.table
  base := (-443859536853426537216818931073186165291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-2874474052574737709953023317520000000000000)
      constant := (36880736189875380722227159321132264902476200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315056334370792319461/100000000000000000000)
  centralHi := (157528167185396159731/50000000000000000000)
  directionLo := (159437669232745529277/50000000000000000000)
  directionHi := (63775067693098211711/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree043.table
  base := (-1083677474375373309893504779814045806721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1165084376351933057730514422360000000000000)
      constant := (15164877179406331807237195638378554807664352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree043.table
  base := (-1748899235216062332099817983985321169119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-26449282210364076967229474181720000000000000)
      constant := (347439308748986917107456828038925449265068050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159437669232745529277/50000000000000000000)
  centralHi := (63775067693098211711/20000000000000000000)
  directionLo := (40331142808590405479/12500000000000000000)
  directionHi := (322649142468723243833/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree044.table
  base := (-8528723075683027395757492560008298827037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1190575635221996347312689581280000000000000)
      constant := (15857009764677579744043523117199701242226668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree044.table
  base := (-8601042722387584905386825572956633887111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-27028297947555514544881738505760000000000000)
      constant := (363301682426309905502108285895729126551440090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40331142808590405479/12500000000000000000)
  centralHi := (322649142468723243833/100000000000000000000)
  directionLo := (65275862856073670377/20000000000000000000)
  directionHi := (163189657140184175943/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree045.table
  base := (-1675567261345257504658084872915034035799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-135118543788006626321651637800000000000000)
      constant := (1840486565860365412019948990666699319284020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree045.table
  base := (-8447464496713546013118875829099620798607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1022493099435072300834592697400000000000000)
      constant := (14056045670483763085235636383677011376041790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65275862856073670377/20000000000000000000)
  centralHi := (163189657140184175943/50000000000000000000)
  directionLo := (82516833299501852477/25000000000000000000)
  directionHi := (330067333198007409909/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree046.table
  base := (-8217354430349480306899694295413547175297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1241558152962122926477039899120000000000000)
      constant := (17286963745683657015619746051625112301689308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree046.table
  base := (-1656871650253040332521381758699868504039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-28186329421938389700186267153840000000000000)
      constant := (396073477409954335095300066264409532558642050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82516833299501852477/25000000000000000000)
  centralHi := (330067333198007409909/100000000000000000000)
  directionLo := (66742919354420040861/20000000000000000000)
  directionHi := (166857298386050102153/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree047.table
  base := (-4023918831651974612432186249969003174847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1267049411832186216059215058040000000000000)
      constant := (18024743555695636301146091998767231771411016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree047.table
  base := (-4056142789289500693870526951986556927331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-28765345159129827277838531477880000000000000)
      constant := (412981960457033576761470932766487777777723780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66742919354420040861/20000000000000000000)
  centralHi := (166857298386050102153/50000000000000000000)
  directionLo := (168661213496973289559/50000000000000000000)
  directionHi := (337322426993946579119/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree048.table
  base := (-245931672783491246183356845950800148521/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-143615630078027722849043357440000000000000)
      constant := (2086411059103763738125999132678297580989312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree048.table
  base := (-3965887493890207083707368170101806239997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-3260484544035696095054532866880000000000000)
      constant := (47804250461323077602996789718885674876800540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168661213496973289559/50000000000000000000)
  centralHi := (337322426993946579119/100000000000000000000)
  directionLo := (42611509486765905237/12500000000000000000)
  directionHi := (340892075894127241897/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree049.table
  base := (-7683778769546520337730719467650721486147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1318031929572312795223565375880000000000000)
      constant := (19545813791690194830997858761049574026498708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree049.table
  base := (-7743323856828370075171857065848438443469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-29923376633512702433143060125960000000000000)
      constant := (447841955618429966732230030594296764860790110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/12500000000000000000)
  centralHi := (340892075894127241897/100000000000000000000)
  directionLo := (344424730618648223487/100000000000000000000)
  directionHi := (1345409103979094623/390625000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree050.table
  base := (-7490201143822477504558621494589015524251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1343523188442376084805740534800000000000000)
      constant := (20329069495637211296333935178694795441126964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree050.table
  base := (-3773700134288516748846564629594537738753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-30502392370704140010795324450000000000000000)
      constant := (465792685709488508524036324465056848863220140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344424730618648223487/100000000000000000000)
  centralHi := (1345409103979094623/390625000000000000)
  directionLo := (69584303608227447063/20000000000000000000)
  directionHi := (86980379510284308829/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree051.table
  base := (-227797535034033255576396977838694868587/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-152112716368048819376435077080000000000000)
      constant := (2347494531876011335370983626001647056820864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree051.table
  base := (-7344444737864760751776771991761949846733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-3453489789766175287605287641560000000000000)
      constant := (53787787512007139465087047959367424513794030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/20000000000000000000)
  centralHi := (86980379510284308829/25000000000000000000)
  directionLo := (175691754480944815319/50000000000000000000)
  directionHi := (351383508961889630639/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree052.table
  base := (-354107673704902477747138093450632097761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1394505706182502663970090852640000000000000)
      constant := (21940942733611803305972674434555544889612080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree052.table
  base := (-1783717959075949247542674390695416523397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-31660423845087015166099853098080000000000000)
      constant := (502733825511151288143745543139682850464193720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175691754480944815319/50000000000000000000)
  centralHi := (351383508961889630639/100000000000000000000)
  directionLo := (354811721938116579503/100000000000000000000)
  directionHi := (22175732621132286219/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree053.table
  base := (-1717122194801088510540489626017506763879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1419996965052565953552266011560000000000000)
      constant := (22769531275071538024543470774418479026001424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree053.table
  base := (-6919071720973739768712042134829180323759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-32239439582278452743752117422120000000000000)
      constant := (521723583391515133377694578689494363937755210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354811721938116579503/100000000000000000000)
  centralHi := (22175732621132286219/6250000000000000000)
  directionLo := (89551781696057123199/25000000000000000000)
  directionHi := (358207126784228492797/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree054.table
  base := (-132977896571442925615860983886175705781/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-160609802658069915903826796720000000000000)
      constant := (2623689241193932900331819381962764858843800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree054.table
  base := (-52323527912520244073417322673272177097/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1215498345165551493385347472080000000000000)
      constant := (20039224586392744783070121588606634839947520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89551781696057123199/25000000000000000000)
  centralHi := (358207126784228492797/100000000000000000000)
  directionLo := (361570647776244875501/100000000000000000000)
  directionHi := (180785323888122437751/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree055.table
  base := (-1284743591953823624275664209098312669509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1470979482792692532716616329400000000000000)
      constant := (24471945952480940634681863088487303719488380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree055.table
  base := (-6470236950041055330929395978514230756887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-33397471056661327899056646070200000000000000)
      constant := (560739986932235145261952571688253473086921530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361570647776244875501/100000000000000000000)
  centralHi := (180785323888122437751/50000000000000000000)
  directionLo := (364903166590335744907/100000000000000000000)
  directionHi := (91225791647583936227/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree056.table
  base := (-1238656861527527363381321244521642434273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1496470741662755822298791488320000000000000)
      constant := (25345747879423846398522338768946104361830860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree056.table
  base := (-779734132736399076533283915740575411169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-33976486793852765476708910394240000000000000)
      constant := (580766089270954572669156227615825071335624880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364903166590335744907/100000000000000000000)
  centralHi := (91225791647583936227/25000000000000000000)
  directionLo := (14728221000078743177/4000000000000000000)
  directionHi := (184102762500984289713/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree057.table
  base := (-1191580196605115252839650284069279107011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-169106888948091012431218516360000000000000)
      constant := (2914955321731509992691363222003614417859780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree057.table
  base := (-1500156491758547207280486973870111572809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-3839500281227133672706797190920000000000000)
      constant := (66793013660136736768010665332080759833788760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14728221000078743177/4000000000000000000)
  centralHi := (184102762500984289713/50000000000000000000)
  directionLo := (92869631842268646513/25000000000000000000)
  directionHi := (371478527369074586053/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree058.table
  base := (-714732147834719433078472328924091499277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1547453259402882401463141806160000000000000)
      constant := (27138485589877357757732170984009861648208224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree058.table
  base := (-575878370150976940414296491393934903707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-35134518268235640632013439042320000000000000)
      constant := (621852854633871142398428156033285127279973300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92869631842268646513/25000000000000000000)
  centralHi := (371478527369074586053/100000000000000000000)
  directionLo := (187361471459994466461/50000000000000000000)
  directionHi := (374722942919988932923/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree059.table
  base := (-1368356308581951933088316812040921229093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1572944518272945691045316965080000000000000)
      constant := (28057401158506739069742353868751107343010608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree059.table
  base := (-1378154335032154680343413658917518077483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-35713534005427078209665703366360000000000000)
      constant := (642913064778279452777076822623461241428955080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187361471459994466461/50000000000000000000)
  centralHi := (374722942919988932923/100000000000000000000)
  directionLo := (188969753932301472691/50000000000000000000)
  directionHi := (377939507864602945383/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree060.table
  base := (-2612430790393731969616525884422314455109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-177603975238112108958610236000000000000000)
      constant := (3221259485503390173207324178924621484359128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree060.table
  base := (-1052476399069328648504857647871865760641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-4032505526957612865257551965600000000000000)
      constant := (73813060748151808646006296456057660407711550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188969753932301472691/50000000000000000000)
  centralHi := (377939507864602945383/100000000000000000000)
  directionLo := (381128927345142957543/100000000000000000000)
  directionHi := (47641115918142869693/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree061.table
  base := (-4972407706603687897402644139862988495739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1623927036013072270209667282920000000000000)
      constant := (29940279529504984527865983778649932414153396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree061.table
  base := (-39127482478860523556993060636427380071/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-36871565479809953364970232014440000000000000)
      constant := (686066106026126071230730493186929209234238720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381128927345142957543/100000000000000000000)
  centralHi := (47641115918142869693/12500000000000000000)
  directionLo := (384291877241219147413/100000000000000000000)
  directionHi := (192145938620609573707/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree062.table
  base := (-1179072752660567087422983151026943450759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1649418294883135559791842441840000000000000)
      constant := (30904225452070989582000676396992120143090704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree062.table
  base := (-4750650578432417697206020959748878316263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-37450581217001390942622496338480000000000000)
      constant := (708158559635065190024507182306899408563826970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384291877241219147413/100000000000000000000)
  centralHi := (192145938620609573707/50000000000000000000)
  directionLo := (193714502921116643589/50000000000000000000)
  directionHi := (387429005842233287179/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree063.table
  base := (-4456725627758047940324747514144761996953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-186101061528133205486001955640000000000000)
      constant := (3542573936485972487341993063628420952012188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree063.table
  base := (-897918621220712458576817180103322533851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1408503590896030685936102246760000000000000)
      constant := (27059064270956908426727363285582501619922350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193714502921116643589/50000000000000000000)
  centralHi := (387429005842233287179/100000000000000000000)
  directionLo := (390540935398867275031/100000000000000000000)
  directionHi := (48817616924858409379/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree064.table
  base := (-838782640505172222252480142871735008517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1700400812623262138956192759680000000000000)
      constant := (32877092199208578900187160079243087698466940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree064.table
  base := (-4225345466045589786118261678589646617179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-38608612691384266097927024986560000000000000)
      constant := (753374470966592296445256318771606386240085010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390540935398867275031/100000000000000000000)
  centralHi := (48817616924858409379/12500000000000000000)
  directionLo := (39362826356416939827/10000000000000000000)
  directionHi := (393628263564169398271/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree065.table
  base := (-3928043617831522649957698540321399859931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1725892071493325428538367918600000000000000)
      constant := (33885998928791579791980042888673429605042484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree065.table
  base := (-3958095999762765049416914166669332678307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-39187628428575703675579289310600000000000000)
      constant := (776497614030714042248627936132647840530571330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39362826356416939827/10000000000000000000)
  centralHi := (393628263564169398271/100000000000000000000)
  directionLo := (79338312946738210191/20000000000000000000)
  directionHi := (99172891183422762739/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree066.table
  base := (-57176495014969355658816665632044812371/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-194598147818154302013393675280000000000000)
      constant := (3878875464451174093116606164338196528033024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree066.table
  base := (-3688021958470320600289968115174452695261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-4418516018418571250359061514960000000000000)
      constant := (88884891214968602954730069082890299257426510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79338312946738210191/20000000000000000000)
  centralHi := (99172891183422762739/25000000000000000000)
  directionLo := (399731391293184760287/100000000000000000000)
  directionHi := (12491605977912023759/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree067.table
  base := (-3387837769647878527104568066461242278841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1776874589233452007702718236440000000000000)
      constant := (35948726891416811151543389176172395277961724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree067.table
  base := (-3415290156171965194066358724987454561813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-40345659902958578830883817958680000000000000)
      constant := (823773556559259445385267938098986161804931470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399731391293184760287/100000000000000000000)
  centralHi := (12491605977912023759/3125000000000000000)
  directionLo := (6292941793461549389/1562500000000000000)
  directionHi := (402748274781539160897/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree068.table
  base := (-3113828440476995201409900229288400887113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1802365848103515297284893395360000000000000)
      constant := (37002536354823578415223117277585617568063932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree068.table
  base := (-628011516855519656223014563030455372229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-40924675640150016408536082282720000000000000)
      constant := (847926093741298080071921005868142655742472550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6292941793461549389/1562500000000000000)
  centralHi := (402748274781539160897/100000000000000000000)
  directionLo := (1267946021799639097/312500000000000000)
  directionHi := (405742726975884511041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree069.table
  base := (-2837417001739734348280585606324988701231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-203095234108175398540785394920000000000000)
      constant := (4230144688353585798757047574739700045195076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree069.table
  base := (-2862471990026613835191888907477038851669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-4611521264149050442909816289640000000000000)
      constant := (96935723645063269059309738272313066503349790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1267946021799639097/312500000000000000)
  centralHi := (405742726975884511041/100000000000000000000)
  directionLo := (408715240905141862741/100000000000000000000)
  directionHi := (204357620452570931371/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree070.table
  base := (-2558744052915269740105358156587104484639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1853348365843641876449243713200000000000000)
      constant := (39155019350911642216508327438862864238552996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree070.table
  base := (-258267242084859282869832248473955778201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-42082707114532891563840610930800000000000000)
      constant := (897259701123655509183222626305960958196571900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408715240905141862741/100000000000000000000)
  centralHi := (204357620452570931371/50000000000000000000)
  directionLo := (82333258359540012997/20000000000000000000)
  directionHi := (205833145898850032493/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree071.table
  base := (-1138970996332635819174559151509570161333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1878839624713705166031418872120000000000000)
      constant := (40253683055659868368895078660976310948384024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree071.table
  base := (-2300789736667520475350146430144630109411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-42661722851724329141492875254840000000000000)
      constant := (922440552699017914997116175398176849611377090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82333258359540012997/20000000000000000000)
  centralHi := (205833145898850032493/50000000000000000000)
  directionLo := (103649084492094683991/25000000000000000000)
  directionHi := (82919267593675747193/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree072.table
  base := (-24939193714983443591951374542895135197/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-211592320398196495068177114560000000000000)
      constant := (4596365424564825441108587673106273556736960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree072.table
  base := (-252118386504679945927014825052795691947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1601508836626509878486857021440000000000000)
      constant := (35109776584313624604212244365315329033932720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103649084492094683991/25000000000000000000)
  centralHi := (82919267593675747193/20000000000000000000)
  directionLo := (208752910824682341189/50000000000000000000)
  directionHi := (417505821649364682379/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree073.table
  base := (-855220985366127379021444022526194042667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1929822142453831745195769189960000000000000)
      constant := (42495832420630520174801962653143114028927976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree073.table
  base := (-108203774367888458874073654318088906429/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-43819754326107204296797403902920000000000000)
      constant := (973829852474633786291023852728423567772680160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208752910824682341189/50000000000000000000)
  centralHi := (417505821649364682379/100000000000000000000)
  directionLo := (420395169769387453609/100000000000000000000)
  directionHi := (42039516976938745361/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree074.table
  base := (-711985984837405499951366723600833340031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-1955313401323895034777944348880000000000000)
      constant := (43639309874270425127587341334160739999517768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree074.table
  base := (-1443838708539420718657665820164504586373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-44398770063298641874449668226960000000000000)
      constant := (1000038118440071966864119664767850751285037870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420395169769387453609/100000000000000000000)
  centralHi := (42039516976938745361/10000000000000000000)
  directionLo := (423264794685021124093/100000000000000000000)
  directionHi := (211632397342510562047/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree075.table
  base := (-1135829602067804489961774139044952343951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-220089406688217591595568834200000000000000)
      constant := (4977524159345961250928942721568820190624196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree075.table
  base := (-144348087949732619457824110630810300431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-4997531755610008828011325839000000000000000)
      constant := (114065409169082861530428059341595816583689680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423264794685021124093/100000000000000000000)
  centralHi := (211632397342510562047/50000000000000000000)
  directionLo := (42611509486765905237/10000000000000000000)
  directionHi := (426115094867659052371/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree076.table
  base := (-26441028241431602638978443108246225753/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2006295919064021613942294666720000000000000)
      constant := (45971051570870873829097209330899300347932544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree076.table
  base := (-8641949861495760612884431326138093131/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-45556801537681517029754196875040000000000000)
      constant := (1053481466464673834613508789038166814456389000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/10000000000000000000)
  centralHi := (426115094867659052371/100000000000000000000)
  directionLo := (428946455549401948579/100000000000000000000)
  directionHi := (21447322777470097429/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree077.table
  base := (-554914192435979798984936594896999601991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2031787177934084903524469825640000000000000)
      constant := (47159308961101755496834994423548708014328324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree077.table
  base := (-286080239354971398071677959880408107991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-46135817274872954607406461199080000000000000)
      constant := (1080716396621618754206995836780179738865054580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428946455549401948579/100000000000000000000)
  centralHi := (21447322777470097429/5000000000000000000)
  directionLo := (2158796246654116553/500000000000000000)
  directionHi := (431759249330823310601/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree078.table
  base := (-52464080299273028963326136358111670497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-228586492978238688122960553840000000000000)
      constant := (5373609608356396253063236509932837766590060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree078.table
  base := (-278766750201422072620677162643299392817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-5190537001340488020562080613680000000000000)
      constant := (123143711520194813246141674123146103054646470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2158796246654116553/500000000000000000)
  centralHi := (431759249330823310601/100000000000000000000)
  directionLo := (434553836753326844949/100000000000000000000)
  directionHi := (8691076735066536899/2000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree079.table
  base := (3948325775205773011499481300320499277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2082769695674211482688820143480000000000000)
      constant := (49580581166124216257516849806899492303791776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree079.table
  base := (198820859909276083664500077256318853/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-47293848749255829762710989847160000000000000)
      constant := (1136212422415305101980051469185200209461674400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434553836753326844949/100000000000000000000)
  centralHi := (8691076735066536899/2000000000000000000)
  directionLo := (437330566838584957251/100000000000000000000)
  directionHi := (109332641709646239313/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree080.table
  base := (326729742411916243654664535139877113183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2108260954544274772270995302400000000000000)
      constant := (50813590258674844470691052051265035576074588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree080.table
  base := (62356197867850979894934174236174446589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-47872864486447267340363254171200000000000000)
      constant := (1164473391433238133727643020391256506508685450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437330566838584957251/100000000000000000000)
  centralHi := (109332641709646239313/25000000000000000000)
  directionLo := (44008977759734321321/10000000000000000000)
  directionHi := (440089777597343213211/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree081.table
  base := (124607283004887939079231414878772355673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-237083579268259784650352273480000000000000)
      constant := (5784612348838165636100736384862575447113460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree081.table
  base := (608787884936724417008777836183510888483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1794514082356989071037611796120000000000000)
      constant := (44188009368929121739984833624947505326654490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44008977759734321321/10000000000000000000)
  centralHi := (440089777597343213211/100000000000000000000)
  directionLo := (221415898254845286527/50000000000000000000)
  directionHi := (88566359301938114611/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree082.table
  base := (230109566450543225879482716440383426753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2159243472284401351435345620240000000000000)
      constant := (53324341347833621449274828510707415213452432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree082.table
  base := (453429614370002012717478857014563038463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-49030895960830142495667782819280000000000000)
      constant := (1222020952626104992978666907850579592122310060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221415898254845286527/50000000000000000000)
  centralHi := (88566359301938114611/20000000000000000000)
  directionLo := (222778470489363596657/50000000000000000000)
  directionHi := (89111388195745438663/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree083.table
  base := (1218870923416153036420790837411972454089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2184734731154464641017520779160000000000000)
      constant := (54602078566177393981858084169511831008347204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree083.table
  base := (602965923129338762027693264153331642769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-49609911698021580073320047143320000000000000)
      constant := (1251307439256957014602306982901354397261285780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222778470489363596657/50000000000000000000)
  centralHi := (89111388195745438663/20000000000000000000)
  directionLo := (224132759379704451599/50000000000000000000)
  directionHi := (448265518759408903199/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree084.table
  base := (1518273770886531269502197747176914300899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-245580665558280881177743993120000000000000)
      constant := (6210524512484837084996744780828707657203596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree084.table
  base := (1505946282618458242936012162531953607419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-5576547492801446405663590163040000000000000)
      constant := (142326184966132686627540461201283875824667710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224132759379704451599/50000000000000000000)
  centralHi := (448265518759408903199/100000000000000000000)
  directionLo := (450957828364208533963/100000000000000000000)
  directionHi := (112739457091052133491/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree085.table
  base := (1818589726589198388537268666447655497669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2235717248894591220181871097000000000000000)
      constant := (57202265431453572866900589299117115597916084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree085.table
  base := (1806846583527933526930109594864272134597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-50767943172404455228624575791400000000000000)
      constant := (1310905583617840443864669564313490060429023570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450957828364208533963/100000000000000000000)
  centralHi := (112739457091052133491/25000000000000000000)
  directionLo := (453634159447107720361/100000000000000000000)
  directionHi := (226817079723553860181/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree086.table
  base := (423953007607339723758573516004056812499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2261208507764654509764046255920000000000000)
      constant := (58524711088357962879757350087940730226249820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree086.table
  base := (2108580089143585700378266101508545378783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-51346958909595892806276840115440000000000000)
      constant := (1341217153370422557935439099100885921756814230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453634159447107720361/100000000000000000000)
  centralHi := (226817079723553860181/50000000000000000000)
  directionLo := (456294793167317369807/100000000000000000000)
  directionHi := (28518424572957335613/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree087.table
  base := (2421749087688285585065457618839572301461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-254077751848301977705135712760000000000000)
      constant := (6651339528982804103781517562960358289205844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree087.table
  base := (2411097240073546500883898929852394163789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-5769552738531925598214344937720000000000000)
      constant := (152430037089981456507514613682680715474741010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456294793167317369807/100000000000000000000)
  centralHi := (28518424572957335613/6250000000000000000)
  directionLo := (229470001267009804933/50000000000000000000)
  directionHi := (458940002534019609867/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree088.table
  base := (170280888130464987805666245231991479797/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2312191025504781088928396573760000000000000)
      constant := (61214297732958960328360795596293627092363072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree088.table
  base := (339293924350658638689628318686643172413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-52504990383978767961581368763520000000000000)
      constant := (1402865087156446932837913551403585447757236240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229470001267009804933/50000000000000000000)
  centralHi := (458940002534019609867/100000000000000000000)
  directionLo := (461570052733327699781/100000000000000000000)
  directionHi := (230785026366663849891/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree089.table
  base := (605591103933219427931164627646758152789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2337682284374844378510571732680000000000000)
      constant := (62581435388818682753748707228061416467502020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree089.table
  base := (188643666117774697101129249867159330757/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-53084006121170205539233633087560000000000000)
      constant := (1434201377854946000464430923299592384926610720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461570052733327699781/100000000000000000000)
  centralHi := (230785026366663849891/50000000000000000000)
  directionLo := (58023150179821531789/12500000000000000000)
  directionHi := (464185201438572254313/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree090.table
  base := (1666045374296690052781989018291206581401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-262574838138323074232527432400000000000000)
      constant := (7107051911864721402308966896646329652651208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree090.table
  base := (664579543642341708606740344146378874647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-1987519328087468263588366570800000000000000)
      constant := (54291821201605183200524424013821956831197050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58023150179821531789/12500000000000000000)
  centralHi := (464185201438572254313/100000000000000000000)
  directionLo := (93357139820988279651/20000000000000000000)
  directionHi := (29174106194058837391/6250000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree091.table
  base := (3636860094082918168394844540689686479081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2388664802114970957674922050520000000000000)
      constant := (65360391753950080590224850038749828713246916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree091.table
  base := (3628109696862349703938660573748929567171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-54242037595553080694538161735640000000000000)
      constant := (1497898439429699634432300660237490632949408510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93357139820988279651/20000000000000000000)
  centralHi := (29174106194058837391/6250000000000000000)
  directionLo := (58671473656178556233/12500000000000000000)
  directionHi := (93874357849885689973/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree092.table
  base := (1971113037303510135317480349981343481801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2414156060985034247257097209440000000000000)
      constant := (66772207680986449784010666504638656730689672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree092.table
  base := (3933898003866550076996280391640506431663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-54821053332744518272190426059680000000000000)
      constant := (1530259149176149551985791860918604810209647030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58671473656178556233/12500000000000000000)
  centralHi := (93874357849885689973/20000000000000000000)
  directionLo := (5899296358962159949/1250000000000000000)
  directionHi := (471943708716972795921/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree093.table
  base := (4248153394498146369026420470168655069913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-271071924428344170759919152040000000000000)
      constant := (7577657079694174306731207427765674620279652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree093.table
  base := (530028525428020866905210993774645616983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-6155563229992883983315854487080000000000000)
      constant := (173662363754410175940643500344991744844227760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5899296358962159949/1250000000000000000)
  centralHi := (471943708716972795921/100000000000000000000)
  directionLo := (474501687933617209647/100000000000000000000)
  directionHi := (29656355495851075603/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree094.table
  base := (569326102056053873701255018780149174703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2465138578725160826421447527280000000000000)
      constant := (69640508666190354362872920461268682962314464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree094.table
  base := (1136766971764093580622092955798234189437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-55979084807127393427494954707760000000000000)
      constant := (1596004787019457879847788512541210278773775880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474501687933617209647/100000000000000000000)
  centralHi := (29656355495851075603/6250000000000000000)
  directionLo := (477045951147447471453/100000000000000000000)
  directionHi := (238522975573723735727/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree095.table
  base := (4861561041446550244601759221631534208813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2490629837595224116003622686200000000000000)
      constant := (71096991401050398930926601160103735231517268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree095.table
  base := (2427193277113555859683872480880563179381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-56558100544318831005147219031800000000000000)
      constant := (1629389664160014232111094333717876512350597220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477045951147447471453/100000000000000000000)
  centralHi := (238522975573723735727/50000000000000000000)
  directionLo := (479576716658027328757/100000000000000000000)
  directionHi := (239788358329013664379/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree096.table
  base := (258449029785904876011150704444300241789/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-279569010718365267287310871680000000000000)
      constant := (8063151206752424869627320072995544019343120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree096.table
  base := (1290538874998603917850877663110621017709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-6348568475723363175866609261760000000000000)
      constant := (184790653551150849984175907366335823566375240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479576716658027328757/100000000000000000000)
  centralHi := (239788358329013664379/50000000000000000000)
  directionLo := (241047098517496583667/50000000000000000000)
  directionHi := (96418839406998633467/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree097.table
  base := (1369209931065234810005130231983910662499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2541612355335350695167973004040000000000000)
      constant := (74054616046174552241278440734170683135399856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree097.table
  base := (85474182957463476178602457966356680301/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-57716132018701706160451747679880000000000000)
      constant := (1697183418538272827887691269894481930306803840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241047098517496583667/50000000000000000000)
  centralHi := (96418839406998633467/20000000000000000000)
  directionLo := (96919719865285579037/20000000000000000000)
  directionHi := (242299299663213947593/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree098.table
  base := (723139036323856521561624195940550719347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2567103614205413984750148162960000000000000)
      constant := (75555756016345152138490235089570878607171936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree098.table
  base := (72236721966889094479572007561941158001/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-58295147755893143738104012003920000000000000)
      constant := (1731592253299731929297221313803749787038464800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96919719865285579037/20000000000000000000)
  centralHi := (242299299663213947593/50000000000000000000)
  directionLo := (487090125257592129441/100000000000000000000)
  directionHi := (243545062628796064721/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree099.table
  base := (6093773682335183789068757321645782484903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-288066097008386363814702591320000000000000)
      constant := (8563531098359800891916964826051583129939612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree099.table
  base := (6087901716197209216464285752520561802673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-2180524573817947456139121345480000000000000)
      constant := (65420087661594099878005184512917616854080190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487090125257592129441/100000000000000000000)
  centralHi := (243545062628796064721/50000000000000000000)
  directionLo := (122392242855138131957/25000000000000000000)
  directionHi := (489568971420552527829/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree100.table
  base := (6402800722333408269885394528930213330181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2618086131945540563914498480800000000000000)
      constant := (78602686818475940978050738733041487679886516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree100.table
  base := (6397217066374255444956331167928379077801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-59453179230276018893408540652000000000000000)
      constant := (1801433740987451391990583734746021987053018810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122392242855138131957/25000000000000000000)
  centralHi := (489568971420552527829/100000000000000000000)
  directionLo := (246017664727605873919/50000000000000000000)
  directionHi := (492035329455211747839/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree101.table
  base := (671217158492334925189920903611435127727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2643577390815603853496673639720000000000000)
      constant := (80148476030334512641814827923785116645981720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree101.table
  base := (6706862614074252230682529794143572228211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-60032194967467456471060804976040000000000000)
      constant := (1836866358505979523799893485179290293504850910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246017664727605873919/50000000000000000000)
  centralHi := (492035329455211747839/100000000000000000000)
  directionLo := (494489386222211803993/100000000000000000000)
  directionHi := (247244693111105901997/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree102.table
  base := (7021865717110578214361772023760649483647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-296563183298407460342094310960000000000000)
      constant := (9078794086767347065755334174355042597934588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree102.table
  base := (3508409206532377386359446012271670309209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-6734578967184321560968118811120000000000000)
      constant := (208071133695797423538368977951912900655657620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494489386222211803993/100000000000000000000)
  centralHi := (247244693111105901997/50000000000000000000)
  directionLo := (24846566198407615211/5000000000000000000)
  directionHi := (496931323968152304221/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree103.table
  base := (916482970542017775559183079152262738813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2694559908555730432661023957560000000000000)
      constant := (83284698373426651521699491390360851668778144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree103.table
  base := (1831766422806860024475449757221831715711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-61190226441850331626365333624120000000000000)
      constant := (1908755260050627414518603152657304734758903640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24846566198407615211/5000000000000000000)
  centralHi := (496931323968152304221/100000000000000000000)
  directionLo := (124840330120884244739/25000000000000000000)
  directionHi := (499361320483536978957/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree104.table
  base := (7642147500574390175676177753300398809873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2720051167425793722243199116480000000000000)
      constant := (84875130151759172993843187459278814357155428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree104.table
  base := (7637586781422596760428338556248297977189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-61769242179041769204017597948160000000000000)
      constant := (1945211514560948165548640179526305121361523090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124840330120884244739/25000000000000000000)
  centralHi := (499361320483536978957/100000000000000000000)
  directionLo := (250889774626917944091/50000000000000000000)
  directionHi := (501779549253835888183/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree105.table
  base := (7952699762508313578338347623046795650307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-305060269588428556869486030600000000000000)
      constant := (9608937944224919522271373275617187182601228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree105.table
  base := (7948365056424807163329820939553095061759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-6927584212914800753518873585800000000000000)
      constant := (220223217036120719631320804838209778555558310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250889774626917944091/50000000000000000000)
  centralHi := (501779549253835888183/100000000000000000000)
  directionLo := (252093089802013267969/50000000000000000000)
  directionHi := (504186179604026535939/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree106.table
  base := (8263504387544550541380280492518724711911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2771033685165920301407549434320000000000000)
      constant := (88100631830368598614138138479190674089628796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree106.table
  base := (412969243384503962289803839008437967849/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-62927273653424644359322126596240000000000000)
      constant := (2019147563667721714349088107497160695079153800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252093089802013267969/50000000000000000000)
  centralHi := (504186179604026535939/100000000000000000000)
  directionLo := (126645344209238671917/25000000000000000000)
  directionHi := (506581376836954687669/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree107.table
  base := (4287273077722038624954877010987629757293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2796524944035983590989724593240000000000000)
      constant := (89735700600863536877594404450956109342525096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree107.table
  base := (857063148772880211682855409942233874669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-63506289390616081936974390920280000000000000)
      constant := (2056627333659587293728533944283398094384818900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126645344209238671917/25000000000000000000)
  centralHi := (506581376836954687669/100000000000000000000)
  directionLo := (508965302365834835317/100000000000000000000)
  directionHi := (254482651182917417659/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree108.table
  base := (8885810733357675089155918738381040290567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-313557355878449653396877750240000000000000)
      constant := (10153960810391835402297711868313524161162268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree108.table
  base := (8882091055872186700533522589463206974077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-2373529819548426648689876120160000000000000)
      constant := (77572157484205240580324104901971896209222310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508965302365834835317/100000000000000000000)
  centralHi := (254482651182917417659/50000000000000000000)
  directionLo := (127834528460297715711/25000000000000000000)
  directionHi := (102267622768238172569/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree109.table
  base := (4598642312033782497861711726015828838327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2847507461776110170154074911080000000000000)
      constant := (93050471422457703797110912927958139676359544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree109.table
  base := (459687526361617827321323725145769090907/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-64664320864998957092278919568360000000000000)
      constant := (2132610308343225140244846320431315459272693400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127834528460297715711/25000000000000000000)
  centralHi := (102267622768238172569/20000000000000000000)
  directionLo := (128424991318129854079/25000000000000000000)
  directionHi := (513699965272519416317/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree110.table
  base := (9508955117248185686710501449397766953513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2872998720646173459736250070000000000000000)
      constant := (94730172530085372200704459188678319610326468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree110.table
  base := (9505597624668021721587947921409802522177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-65243336602190394669931183892400000000000000)
      constant := (2171113492524153782611155644363741940042963370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128424991318129854079/25000000000000000000)
  centralHi := (513699965272519416317/100000000000000000000)
  directionLo := (516051007144941673327/100000000000000000000)
  directionHi := (32253187946558854583/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree111.table
  base := (9820810243570001885842162100610707231869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-322054442168470749924269469880000000000000)
      constant := (10713861131723740062390460659367442828927476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree111.table
  base := (4908810396789371749784993489217829959127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-7313594704375759138620383135160000000000000)
      constant := (245550866139677896377695106655405209392642860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516051007144941673327/100000000000000000000)
  centralHi := (32253187946558854583/6250000000000000000)
  directionLo := (64798923316386692591/12500000000000000000)
  directionHi := (518391386531093540729/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree112.table
  base := (1266604841435062719010522394029339939543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2923981238386300038900600387840000000000000)
      constant := (98134203982966678453262741019720449902588384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree112.table
  base := (1012980915936122019958572274914734239627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-66401368076573269825235712540480000000000000)
      constant := (2249143207733638320247709903206905347340978700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64798923316386692591/12500000000000000000)
  centralHi := (518391386531093540729/100000000000000000000)
  directionLo := (520721247198489700041/100000000000000000000)
  directionHi := (260360623599244850021/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree113.table
  base := (5222514983253108279769995996574084721923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-2949472497256363328482775546760000000000000)
      constant := (99858533540323381001817968262918334099978456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree113.table
  base := (10442152487370833411803026580831330796187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-66980383813764707402887976864520000000000000)
      constant := (2288669721663703400244553450079819377944911470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520721247198489700041/100000000000000000000)
  centralHi := (260360623599244850021/50000000000000000000)
  directionLo := (104608145942516657327/20000000000000000000)
  directionHi := (130760182428145821659/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree114.table
  base := (134467174411608815399672916317772834267/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-330551528458491846451661189520000000000000)
      constant := (11288637610859767147603926671161687306965440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree114.table
  base := (10754641145240925112236889754593274067783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-7506599950106238331171137909840000000000000)
      constant := (258726369916119923821150971495009394666100470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104608145942516657327/20000000000000000000)
  centralHi := (130760182428145821659/25000000000000000000)
  directionLo := (262674985767865129141/50000000000000000000)
  directionHi := (525349971535730258283/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree115.table
  base := (11069861277696024516323540936506984482281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3000455014996489907647125864600000000000000)
      constant := (103351818516340378476004618514839251441362116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree115.table
  base := (2213453213484192767453040732487041003227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-68138415288147582558192505512600000000000000)
      constant := (2368746023134670132199591875360222516063069350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262674985767865129141/50000000000000000000)
  centralHi := (525349971535730258283/100000000000000000000)
  directionLo := (527649107122255614119/100000000000000000000)
  directionHi := (13191227678056390353/2500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree116.table
  base := (5691241538219641691220211069780487062967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3025946273866553197229301023520000000000000)
      constant := (105120773277013523367440450747184195068533624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree116.table
  base := (5690009360901467081897336010695249224261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-68717431025339020135844769836640000000000000)
      constant := (2409295796421468361179547275806030303743302820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527649107122255614119/100000000000000000000)
  centralHi := (13191227678056390353/2500000000000000000)
  directionLo := (66242283501225938063/12500000000000000000)
  directionHi := (105987653601961500901/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree117.table
  base := (11695231001471486848400583605874510398723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-339048614748512942979052909160000000000000)
      constant := (11878289164360067464821508508708498041594892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree117.table
  base := (11692891078312978352193601706744385780573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-2566535065278905841240630894840000000000000)
      constant := (90747653429670895428189750865240331573417190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66242283501225938063/12500000000000000000)
  centralHi := (105987653601961500901/20000000000000000000)
  directionLo := (106443516581434973851/20000000000000000000)
  directionHi := (66527197863396858657/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree118.table
  base := (6004048595826518668490624115632979285043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3076928791606679776393651341360000000000000)
      constant := (108703305840020604411083976032665574508523096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree118.table
  base := (6002937789676280253483208808482347502439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-69875462499721895291149298484720000000000000)
      constant := (2491418555551952764268968452194357402953951180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106443516581434973851/20000000000000000000)
  centralHi := (66527197863396858657/12500000000000000000)
  directionLo := (133621794444683626059/25000000000000000000)
  directionHi := (534487177778734504237/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree119.table
  base := (12321074244015006750988835219949895072849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3102420050476743065975826500280000000000000)
      constant := (110516883092846633639012680201403196222622564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree119.table
  base := (12318965111980238676933112062081910594841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-70454478236913332868801562808760000000000000)
      constant := (2532991529512501556322627006075760347581821210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133621794444683626059/25000000000000000000)
  centralHi := (534487177778734504237/100000000000000000000)
  directionLo := (268373587962842168199/50000000000000000000)
  directionHi := (536747175925684336399/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree120.table
  base := (3158538796759411021273570852891837055177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-347545701038534039506444628800000000000000)
      constant := (12482814887415998203443093653646269392882832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree120.table
  base := (2526430596346308812674267233263334743779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-7892610441567196716272647459200000000000000)
      constant := (286100617673360481443903759157368500634700550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268373587962842168199/50000000000000000000)
  centralHi := (536747175925684336399/100000000000000000000)
  directionLo := (269498849032105570567/50000000000000000000)
  directionHi := (107799539612842228227/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree121.table
  base := (6473666727743782260039322314275228953823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3153402568216869645140176818120000000000000)
      constant := (114188658285364253133517581942512816484675256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree121.table
  base := (6472716443990251281736564487805235685293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-71612509711296208024106091456840000000000000)
      constant := (2617160639091674055263214482843238481810174660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269498849032105570567/50000000000000000000)
  centralHi := (107799539612842228227/20000000000000000000)
  directionLo := (270619431200366461311/50000000000000000000)
  directionHi := (541238862400732922623/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree122.table
  base := (3315150716680674545906884036121847806091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3178893827086932934722351977040000000000000)
      constant := (116046855766132327031198579602341546084077104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree122.table
  base := (13258798900752014488257089992619337609999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-72191525448487645601758355780880000000000000)
      constant := (2659756764803510892378794022953677663464099190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270619431200366461311/50000000000000000000)
  centralHi := (541238862400732922623/100000000000000000000)
  directionLo := (543470784704348660379/100000000000000000000)
  directionHi := (27173539235217433019/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree123.table
  base := (13573957598379380461136490821908330626281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-356042787328555136033836348440000000000000)
      constant := (13102214024382568177545008338372633322505124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree123.table
  base := (13572245438899654389800030714818870229723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-8085615687297675908823402233880000000000000)
      constant := (300299325741669582192117185562287698320675070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543470784704348660379/100000000000000000000)
  centralHi := (27173539235217433019/5000000000000000000)
  directionLo := (545693578376621068957/100000000000000000000)
  directionHi := (272846789188310534479/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree124.table
  base := (6943696083680480032201230721177003602691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3229876344827059513886702294880000000000000)
      constant := (119807869447905133387261758571684744259393752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree124.table
  base := (3471441812392121052698674618591656786967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-73349556922870520757062884428960000000000000)
      constant := (2745972135451407597487577549503020967989773080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545693578376621068957/100000000000000000000)
  centralHi := (272846789188310534479/50000000000000000000)
  directionLo := (68488419314851423867/12500000000000000000)
  directionHi := (547907354518811390937/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree125.table
  base := (1775112676256500507721263799840315496123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3255367603697122803468877453800000000000000)
      constant := (121710685265628230813729038027479010862883424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree125.table
  base := (2839871877773441593710965536024666095999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-73928572660061958334715148753000000000000000)
      constant := (2789591372128103015908386786152149897688795950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68488419314851423867/12500000000000000000)
  centralHi := (547907354518811390937/100000000000000000000)
  directionLo := (550112221996679016513/100000000000000000000)
  directionHi := (275056110998339508257/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree126.table
  base := (3628620115921651933446857997998370322381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-364539873618576232561228068080000000000000)
      constant := (13736485944172537034156293467507973925158096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree126.table
  base := (7256508601839226176265547252531053774021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 300000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (481)
      square := (18208042050045206844410827800000000000000)
      linear := (-2759540311009385033791385669520000000000000)
      constant := (104946356960595830467034719544743863226441260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550112221996679016513/100000000000000000000)
  centralHi := (275056110998339508257/50000000000000000000)
  directionLo := (276154143751476434569/50000000000000000000)
  directionHi := (552308287502952869139/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree127.table
  base := (118624997990427899568211170826312465877/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3306350121437249382633227771640000000000000)
      constant := (125560933978818334657455159036683406096446500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree127.table
  base := (1853342039317518921087590905650996637801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-75086604134444833490019677401080000000000000)
      constant := (2877852929327996544137071029090604458212950480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276154143751476434569/50000000000000000000)
  centralHi := (552308287502952869139/100000000000000000000)
  directionLo := (554495655617575990489/100000000000000000000)
  directionHi := (55449565561757599049/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree128.table
  base := (15141829952724461794296746379511272101803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (819)
      previous := (0)
      next := (585)
      square := (21849650460054248213292993360000000000000)
      linear := (-3331841380307312672215402930560000000000000)
      constant := (127508366554168320333323742259102405795664908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree128.table
  base := (15140512599534959958454182889809736414267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8100000000000000000000000000000000000000000
      center := (18603)
      previous := (0)
      next := (12987)
      square := (491617135351220584799092350600000000000000)
      linear := (-75665619871636271067671941725120000000000000)
      constant := (2922495242965077330992313860461001886495556270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell171.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554495655617575990489/100000000000000000000)
  centralHi := (55449565561757599049/10000000000000000000)
  directionLo := (69584303608227447063/12500000000000000000)
  directionHi := (111334885773163915301/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree129.table
  base := (3863898003499156066735852659069454935827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (91)
      previous := (0)
      next := (65)
      square := (2427738940006027579254777040000000000000)
      linear := (-373036959908597329088619787720000000000000)
      constant := (14385630119710053966732534255910111278973232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree129.table
  base := (123634737433026687172179634663864755259/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 900000000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (1443)
      square := (54624126150135620533232483400000000000000)
      linear := (-8471626178758634293924911783240000000000000)
      constant := (329719841744989644885910891784834478496663750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell171.Kernel129
