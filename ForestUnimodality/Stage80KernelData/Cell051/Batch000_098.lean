import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell051.Parameters
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch000_049
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree000.table
  base := (13543273685561276105545403/400000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (728809046269649069005325250000000000000)
      linear := (19680115793699031606633909000000000000)
      constant := (169290921069515951319317537500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree000.table
  base := (13543273685561276105545403/400000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (728809046269649069005325250000000000000)
      linear := (19680115793699031606633909000000000000)
      constant := (169290921069515951319317537500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree001.table
  base := (98997184070909034217717191104312447397491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-15554026096656869726064051854920944000000000000)
      constant := (2240116743059915831413559932831006878843745758419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree001.table
  base := (19761165808758388730067968674904673363361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-15597326464118365251376330741336569000000000000)
      constant := (2235814321295408195027339764164840069468743106245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6247497085982211447/12500000000000000000)
  directionHi := (49979976687857691577/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree002.table
  base := (11869447113935748609045430687221961578069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-31552645866330236418444854807766069000000000000)
      constant := (1355827812435257490862565476457124883039054908105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree002.table
  base := (23652251162440680373015580840440672197427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-63278493202506454938138825161194638000000000000)
      constant := (2702035043007916712292058072431548473890615669215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6247497085982211447/12500000000000000000)
  centralHi := (49979976687857691577/100000000000000000000)
  directionLo := (14136472175811893999/20000000000000000000)
  directionHi := (17670590219764867499/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree003.table
  base := (73222441932633489416514693371706456693523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-95102531272007206221651315521222388000000000000)
      constant := (1722829321599130623505979408585397991271488334707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree003.table
  base := (36423680630021283570743150337837078852691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-47681166738388089686762494419858069000000000000)
      constant := (857365775486698508044351647020905320894852055219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14136472175811893999/20000000000000000000)
  centralHi := (17670590219764867499/25000000000000000000)
  directionLo := (17313571796895515133/20000000000000000000)
  directionHi := (43283929492238787833/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree004.table
  base := (46519040603091401435480623447068888229267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-127099770811353939606412921426912638000000000000)
      constant := (1173551151772450613564526491049160679607364860403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree004.table
  base := (23110982468805858065519925090347128437029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-63723086875522951904455576259118819000000000000)
      constant := (583754673843873396433126200631522817645078072261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17313571796895515133/20000000000000000000)
  centralHi := (43283929492238787833/50000000000000000000)
  directionLo := (99959953375715383153/100000000000000000000)
  directionHi := (49979976687857691577/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree005.table
  base := (15159138104785055717642945238155988594851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-79548505175350336495587263666301444000000000000)
      constant := (438542019822392914677244058956095348625176294659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree005.table
  base := (30088737843150372454468337378304433943247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-159530014025315628244297316196759138000000000000)
      constant := (872945990005234104896324545940887561951798466223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99959953375715383153/100000000000000000000)
  centralHi := (49979976687857691577/50000000000000000000)
  directionLo := (111758625387904586243/100000000000000000000)
  directionHi := (27939656346976146561/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree006.table
  base := (20062312011337623791958265575296287471609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-191094249890047406375936133238293138000000000000)
      constant := (730461854385729091146747050702834085937706163481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree006.table
  base := (4970786337783062168631406716508259700701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-95806927149792676339841739937640319000000000000)
      constant := (363962017559891481473752673991440375945747194618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111758625387904586243/100000000000000000000)
  centralHi := (27939656346976146561/25000000000000000000)
  directionLo := (122425440241449774563/100000000000000000000)
  directionHi := (30606360060362443641/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree007.table
  base := (13237062151242153178875130812120624258219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-4552887539375390607361178349877212000000000000)
      constant := (13814058362644728617581709961590807478633545979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree007.table
  base := (13092805666335629762424079417818660758471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-4565259072935817900307543745995962000000000000)
      constant := (13789515169063335628755469194782017174746228311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122425440241449774563/100000000000000000000)
  centralHi := (30606360060362443641/25000000000000000000)
  directionLo := (66117294424438580739/50000000000000000000)
  directionHi := (132234588848877161479/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree008.table
  base := (4223625383211408192790532356913528121081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-127544364484370436572729672524836819000000000000)
      constant := (342422183110500342171705504781575628005093960729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree008.table
  base := (1665255354429892711190920613746085137651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-255781534848124801550455807232323638000000000000)
      constant := (684798535377957124584927417163620769297199899295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66117294424438580739/50000000000000000000)
  centralHi := (132234588848877161479/100000000000000000000)
  directionLo := (14136472175811893999/10000000000000000000)
  directionHi := (141364721758118939991/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree009.table
  base := (245618751974596261081702968082074145329/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-143542984254043803265110475477681944000000000000)
      constant := (368348013783912708496499800083671090432947469610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree009.table
  base := (4806712110348199017371258400022989975611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-287865375122394525985841970910845138000000000000)
      constant := (737711163812851551751555770718455708745937881499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14136472175811893999/10000000000000000000)
  centralHi := (141364721758118939991/100000000000000000000)
  directionLo := (14993993006357307473/10000000000000000000)
  directionHi := (149939930063573074731/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree010.table
  base := (1095294741263458449901314434184862037941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-159541604023717169957491278430527069000000000000)
      constant := (411231054207898946490428988584772815962883472469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree010.table
  base := (2095095102545487415702746834471861664093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-319949215396664250421228134589366638000000000000)
      constant := (824506301115311517650391866309057967100279939837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14993993006357307473/10000000000000000000)
  centralHi := (149939930063573074731/100000000000000000000)
  directionLo := (7902528186787438321/5000000000000000000)
  directionHi := (158050563735748766421/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree011.table
  base := (3397876413950636321752682630779162419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-175540223793390536649872081383372194000000000000)
      constant := (468194214184495244495643299825965496315880363084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree011.table
  base := (-15326298096146868925056821834771811109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-176016527835466987428307149133944069000000000000)
      constant := (469737250159891489335977712924948431004580562038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7902528186787438321/5000000000000000000)
  centralHi := (158050563735748766421/100000000000000000000)
  directionLo := (165764829704333788049/100000000000000000000)
  directionHi := (3315296594086675761/2000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree012.table
  base := (-864325285038627699638363962001483445231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-191538843563063903342252884336217319000000000000)
      constant := (537534061649022704777466771418176932475435471921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree012.table
  base := (-1811993080204320745753327847801998464573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-384116895945203699292000461946409638000000000000)
      constant := (1079238308309251174601896886332876578468845175843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165764829704333788049/100000000000000000000)
  centralHi := (3315296594086675761/2000000000000000000)
  directionLo := (173135717968955151331/100000000000000000000)
  directionHi := (43283929492238787833/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree013.table
  base := (-633918733764947054651152625842259677423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-415074926665474540069267374578124888000000000000)
      constant := (1236407404108103057743255179623106232984999550965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree013.table
  base := (-3248834672325846273980103961784643920281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-416200736219473423727386625624931138000000000000)
      constant := (1241722376934009586258694833992077247135136646471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173135717968955151331/100000000000000000000)
  centralHi := (43283929492238787833/25000000000000000000)
  directionLo := (22525671086820718867/12500000000000000000)
  directionHi := (180205368694565750937/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree014.table
  base := (-174217547597339863180858787106883172727/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-9123921759282066805184264907832962000000000000)
      constant := (28960316327339115310251979372133004879069279825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree014.table
  base := (-4431132157273041261057963315338377774481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-9148664826402921391076995700070462000000000000)
      constant := (29093612447334604226264309095821296972475505279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22525671086820718867/12500000000000000000)
  centralHi := (180205368694565750937/100000000000000000000)
  directionLo := (93503974482456060307/50000000000000000000)
  directionHi := (37401589792982424123/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree015.table
  base := (-2663519462861733308297356825410914168809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-239534702872084003419395293194752694000000000000)
      constant := (811044746999053539225989199668529878689208361719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree015.table
  base := (-2699729022252116197291970299267624517607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-240184208384006436299079476490987069000000000000)
      constant := (814957816669541796881110511192822811114119604537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93503974482456060307/50000000000000000000)
  centralHi := (37401589792982424123/20000000000000000000)
  directionLo := (9678580867795388549/5000000000000000000)
  directionHi := (193571617355907770981/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree016.table
  base := (-3057028710710869450504875904175705134953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-255533322641757370111776096147597819000000000000)
      constant := (922419633930940832908141183332123311714930562423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree016.table
  base := (-6183324360677153215001730562817615609003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-512452257042282597033545116660495638000000000000)
      constant := (1854041540733240447952739091940196388418472745973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9678580867795388549/5000000000000000000)
  centralHi := (193571617355907770981/100000000000000000000)
  directionLo := (199919906751430766307/100000000000000000000)
  directionHi := (49979976687857691577/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree017.table
  base := (-6739301918370487658287219587736287184523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-543063884822861473608313798200885888000000000000)
      constant := (2086789571741009682286954186362350736337856246293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree017.table
  base := (-85068319267308623744504842963931404419/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-272268048658276160734465640169508569000000000000)
      constant := (1048725569131388678846148187515835981695509249160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199919906751430766307/100000000000000000000)
  centralHi := (49979976687857691577/25000000000000000000)
  directionLo := (206072723049945577221/100000000000000000000)
  directionHi := (103036361524972788611/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree018.table
  base := (-1805294212717485177086286562328632898693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-287530562181104103496537702053288069000000000000)
      constant := (1173762315447287386241087640074405678455860697526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree018.table
  base := (-1821064378919474691521925476522193617791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-288309968795411022952158722008769319000000000000)
      constant := (1179864647574559274122669195926369037561481917762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206072723049945577221/100000000000000000000)
  centralHi := (103036361524972788611/50000000000000000000)
  directionLo := (106023541318589204993/50000000000000000000)
  directionHi := (212047082637178409987/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree019.table
  base := (-473443359176103762462341896033611032709/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-303529181950777470188918505006133194000000000000)
      constant := (1313348141678569679416792614231532876235573492952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree019.table
  base := (-3817553927424351949837711537050245846931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-304351888932545885169851803848030069000000000000)
      constant := (1320263969405270010489120336280526998619769156621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106023541318589204993/50000000000000000000)
  centralHi := (212047082637178409987/100000000000000000000)
  directionLo := (43571533516578076857/20000000000000000000)
  directionHi := (108928833791445192143/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree020.table
  base := (-3907151434117956331582667120134152690711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-319527801720450836881299307958978319000000000000)
      constant := (1462002596170053029961336459031431280356773582601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree020.table
  base := (-3935637634491021476501277920016578654219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-320393809069680747387544885687290819000000000000)
      constant := (1469773770804092279307446471687449321473330683029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43571533516578076857/20000000000000000000)
  centralHi := (108928833791445192143/50000000000000000000)
  directionLo := (111758625387904586243/50000000000000000000)
  directionHi := (223517250775809172487/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree021.table
  base := (-7950401050655284190060841241792707248137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-13694955979188743003007351465788712000000000000)
      constant := (66105905584237385420523749183912794207611669383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree021.table
  base := (-1000546295953465915150460452985092554227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-6866035289935012440923223827072481000000000000)
      constant := (33229855185277723326321502796346300774826518772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111758625387904586243/50000000000000000000)
  centralHi := (223517250775809172487/100000000000000000000)
  directionLo := (229037026404236143597/100000000000000000000)
  directionHi := (114518513202118071799/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree022.table
  base := (-7993656459330736239960410536203953469029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-703050082519595140532121827729337138000000000000)
      constant := (3572016859006028514247836279385540747345584639739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree022.table
  base := (-4022338218216433111993650786208963726577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-352477649343950471822931049365812319000000000000)
      constant := (1795615214329516793932833036662463617572225453807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229037026404236143597/100000000000000000000)
  centralHi := (114518513202118071799/50000000000000000000)
  directionLo := (117213435166167665231/50000000000000000000)
  directionHi := (234426870332335330463/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree023.table
  base := (-7953228148037463678337119660310837193531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-735047322058941873916883433635027388000000000000)
      constant := (3922280736209029034666534542292558776913406437221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree023.table
  base := (-4000683437892986229983277604933733183341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-368519569481085334040624131205073069000000000000)
      constant := (1971727083371448584071642291583921051251544818931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117213435166167665231/50000000000000000000)
  centralHi := (234426870332335330463/100000000000000000000)
  directionLo := (239695547734062764001/100000000000000000000)
  directionHi := (119847773867031382001/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree024.table
  base := (-3918661857072164749906273586400842145871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-383522280799144303650822519770358819000000000000)
      constant := (2144897793665302543315247732959623003475048926161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree024.table
  base := (-315306473136504758521151648978070207131/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-769122979236440392516634426088667638000000000000)
      constant := (4313011321090512924132757349550929690701792870525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239695547734062764001/100000000000000000000)
  centralHi := (119847773867031382001/50000000000000000000)
  directionLo := (244850880482899549127/100000000000000000000)
  directionHi := (30606360060362443641/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree025.table
  base := (-306132770954385973942946992870580153341/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-799041801137635340686406645446407888000000000000)
      constant := (4674394778463109565547050147911710491766302223275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree025.table
  base := (-7695947753227736020663498017054813852003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-801206819510710116952020589767189138000000000000)
      constant := (4699735024142055535475036752604423496776075558973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244850880482899549127/100000000000000000000)
  centralHi := (30606360060362443641/12500000000000000000)
  directionLo := (62474970859822114471/25000000000000000000)
  directionHi := (49979976687857691577/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree026.table
  base := (-7407855449237175041069520525776830945667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-831039040676982074071168251352098138000000000000)
      constant := (5075928291253960565647032476430205868114958291997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree026.table
  base := (-7447873357337301550108240951980728690143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-833290659784979841387406753445710638000000000000)
      constant := (5103475074895455491088007698045241628334421275713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62474970859822114471/25000000000000000000)
  centralHi := (49979976687857691577/20000000000000000000)
  directionLo := (254848876420298851503/100000000000000000000)
  directionHi := (15928054776268678219/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree027.table
  base := (-3553458612834719145370083304330279030471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-431518140108164403727964928628894194000000000000)
      constant := (2747130459422145267229666065368265424825118364761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree027.table
  base := (-7144429579822067751684394020785237897783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-865374500059249565822792917124232138000000000000)
      constant := (5524096131992021066287440223137782479584043166953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254848876420298851503/100000000000000000000)
  centralHi := (15928054776268678219/6250000000000000000)
  directionLo := (64925894238358181749/25000000000000000000)
  directionHi := (259703576953432726997/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree028.table
  base := (-3377951147529451715640703506489742294213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-9132995099547709600415219011872231000000000000)
      constant := (60502762468650527276522943128694705722933744267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree028.table
  base := (-3395509073383213356180661118890790413141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-9157738166668564186307949804109731000000000000)
      constant := (60831389438664941068133475715504189097135060219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64925894238358181749/25000000000000000000)
  centralHi := (259703576953432726997/100000000000000000000)
  directionLo := (66117294424438580739/25000000000000000000)
  directionHi := (264469177697754322957/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree029.table
  base := (-3179840342417997883639132984399175765483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-463515379647511137112726534534584444000000000000)
      constant := (3190423840835416498318536670205123083564391657653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree029.table
  base := (-6392511443470352455828066953417748235023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-929542180607789014693565244481275138000000000000)
      constant := (6415505101786721785388003542640783070862861291793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66117294424438580739/25000000000000000000)
  centralHi := (264469177697754322957/100000000000000000000)
  directionLo := (1076601646083416693/400000000000000000)
  directionHi := (269150411520854173251/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree030.table
  base := (-370165465468055104357270006834399575409/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-479513999417184503805107337487429569000000000000)
      constant := (3424446254701609433096187185769732086458712818552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree030.table
  base := (-2976652724406568136979186633996728750383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-480813010441029369564475704079898319000000000000)
      constant := (3443041816393133934465933794138661639829538893553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076601646083416693/400000000000000000)
  centralHi := (269150411520854173251/100000000000000000000)
  directionLo := (136875803277609981283/50000000000000000000)
  directionHi := (273751606555219962567/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree031.table
  base := (-5448769597258348135649817629913596202919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-991025238373715740994976280880549388000000000000)
      constant := (7333315586270492534547616025531976425707491044729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree031.table
  base := (-2738683451523483659594372376389419565927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-496854930578164231782168785919159069000000000000)
      constant := (3686561072661532303948138666460967749081367049657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136875803277609981283/50000000000000000000)
  centralHi := (273751606555219962567/100000000000000000000)
  directionLo := (139138366528864664803/50000000000000000000)
  directionHi := (278276733057729329607/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree032.table
  base := (-617703517002144818704514441556165620351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-511511238956531237189868943393119819000000000000)
      constant := (3917018006913558693613696294670130361860639903364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree032.table
  base := (-2484137771946010049229239811955399775327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-512896850715299093999861867758419819000000000000)
      constant := (3938269884755028950256698264060093464076989765057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139138366528864664803/50000000000000000000)
  centralHi := (278276733057729329607/100000000000000000000)
  directionLo := (282729443516237879981/100000000000000000000)
  directionHi := (141364721758118939991/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree033.table
  base := (-2202227900961753524108009856652630518517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-527509858726204603882249746345964944000000000000)
      constant := (4175490380628133508534681744046336762957507786347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree033.table
  base := (-2214631021000203011777322108903648316671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-528938770852433956217554949597680569000000000000)
      constant := (4198131760618734931005270426091231227745250588961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282729443516237879981/100000000000000000000)
  centralHi := (141364721758118939991/50000000000000000000)
  directionLo := (4486142299311074323/1562500000000000000)
  directionHi := (287113107155908756673/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree034.table
  base := (-1920085521469417188011091817194741787257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-543508478495877970574630549298810069000000000000)
      constant := (4442041948936889242279282872868684129531401027687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree034.table
  base := (-965810534468313102165240819087785636037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-544980690989568818435248031436941319000000000000)
      constant := (4466113765492698930361419975905682396812434817334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4486142299311074323/1562500000000000000)
  centralHi := (287113107155908756673/100000000000000000000)
  directionLo := (29143083977238775133/10000000000000000000)
  directionHi := (291430839772387751331/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree035.table
  base := (-1625704314933536874484210496081660741537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-11418512209501047699326762290850106000000000000)
      constant := (96258019403558236705907055651359834425061039983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree035.table
  base := (-3272847396176917751816675787425291475569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-22898882086804231863385351562293962000000000000)
      constant := (193558619368424083873956385646499576192812192671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29143083977238775133/10000000000000000000)
  centralHi := (291430839772387751331/100000000000000000000)
  directionLo := (295685529642824998203/100000000000000000000)
  directionHi := (73921382410706249551/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree036.table
  base := (-1320273630957828146041581187430129896733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-575505718035224703959392155204500319000000000000)
      constant := (4999266517532924892758971605852851057631735726403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree036.table
  base := (-532090586469086477495438520618249299763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1154129062527677085741268390230925638000000000000)
      constant := (10052644319185470391121654490126186690524051845665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295685529642824998203/100000000000000000000)
  centralHi := (73921382410706249551/25000000000000000000)
  directionLo := (14993993006357307473/5000000000000000000)
  directionHi := (299879860127146149461/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree037.table
  base := (-251216808957682931174807932146020889603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-591504337804898070651772958157345444000000000000)
      constant := (5289888391748717063840829926659654285950162482292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree037.table
  base := (-405640484089410518361827391102031689119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1186212902801946810176654553909447138000000000000)
      constant := (10636995013623299660467028061217125516964137344645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14993993006357307473/5000000000000000000)
  centralHi := (299879860127146149461/100000000000000000000)
  directionLo := (304016329462079285399/100000000000000000000)
  directionHi := (1520081647310396427/500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree038.table
  base := (-27218181998946407670062080068846486027/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-607502957574571437344153761110190569000000000000)
      constant := (5588486673236265196418285895859257557363641718925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree038.table
  base := (-1378030654931912611720660568988216401309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1218296743076216534612040717587968638000000000000)
      constant := (11237380723407431785036873332174129076384080769219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304016329462079285399/100000000000000000000)
  centralHi := (1520081647310396427/500000000000000000)
  directionLo := (154048634081346478867/50000000000000000000)
  directionHi := (61619453632538591547/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree039.table
  base := (-695821581329025507399079493767964604047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1247003154688489608073069128126071388000000000000)
      constant := (11790083179908334628032365229994756918468292786577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree039.table
  base := (-71168390886043053090618489546397439629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-625190291675243129523713440633245069000000000000)
      constant := (5926880999233721201179343437363330213618821521695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154048634081346478867/50000000000000000000)
  centralHi := (61619453632538591547/20000000000000000000)
  directionLo := (156062427187834943923/50000000000000000000)
  directionHi := (312124854375669887847/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree040.table
  base := (-8026127654151683254765802646648265413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-639500197113918170728915367015880819000000000000)
      constant := (6209535291170470159273932532855651855216220528283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree040.table
  base := (-30738305665789239326969454743842457647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1282464423624755983482813044945011638000000000000)
      constant := (12486103232584667366866707865411437282344714504177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156062427187834943923/50000000000000000000)
  centralHi := (312124854375669887847/100000000000000000000)
  directionLo := (316101127471497532841/100000000000000000000)
  directionHi := (158050563735748766421/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree041.table
  base := (338486051718498413696401328751229883753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-655498816883591537421296169968725944000000000000)
      constant := (6531951660745379600369635245622666193939932976777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree041.table
  base := (663383600699414966195667844009567658299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1314548263899025707918199208623533138000000000000)
      constant := (13134372288829960590046079239950705897054741633691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316101127471497532841/100000000000000000000)
  centralHi := (158050563735748766421/50000000000000000000)
  directionLo := (160014000058175167901/50000000000000000000)
  directionHi := (320028000116350335803/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree042.table
  base := (690981681001581315096957759481118012913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-13704029319454385798238305569827981000000000000)
      constant := (140046452011589492965797856733784736129791422433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree042.table
  base := (54775914478011542889648291435308458123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-27482287840271335354154803516368462000000000000)
      constant := (281602860439103316489205641156738305171037151075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160014000058175167901/50000000000000000000)
  centralHi := (320028000116350335803/100000000000000000000)
  directionLo := (323907269026475429069/100000000000000000000)
  directionHi := (32390726902647542907/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree043.table
  base := (209775855679989451630217282146293300937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-687496056422938270806057775874416194000000000000)
      constant := (7200495618377519259689643567064224057765537377165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree043.table
  base := (208614563010910231711849850651872462331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-689357972223782578394485767990288069000000000000)
      constant := (7239290335548939303545635631249155625316858909895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323907269026475429069/100000000000000000000)
  centralHi := (32390726902647542907/10000000000000000000)
  directionLo := (327740624576673935339/100000000000000000000)
  directionHi := (16387031228833696767/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree044.table
  base := (2823307730491791953873171151887030095407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1406989352385223274996877157654522638000000000000)
      constant := (15093196420752950177499060309792595685868610395663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree044.table
  base := (2812580968276742511906135885837340524213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1410799784721834881224357699659097638000000000000)
      constant := (15174470188805507577968217102749224904318560600917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327740624576673935339/100000000000000000000)
  centralHi := (16387031228833696767/5000000000000000000)
  directionLo := (331529659408667576099/100000000000000000000)
  directionHi := (3315296594086675761/1000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree045.table
  base := (3557662950978847401437180672218193546073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1438986591924570008381638763560212888000000000000)
      constant := (15801146434386902625738098946905151314113077057657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree045.table
  base := (1773879924590484917062705067987073990107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-721441812498052302829871931668809569000000000000)
      constant := (7943093694055173008308821756801194705394173147963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331529659408667576099/100000000000000000000)
  centralHi := (3315296594086675761/1000000000000000000)
  directionLo := (33527587616371375873/10000000000000000000)
  directionHi := (335275876163713758731/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree046.table
  base := (4299968397486461647506804361574250821709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1470983831463916741766400369465903138000000000000)
      constant := (16524821943802074506338298355980792652481485414381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree046.table
  base := (2145415112853357747408230871628584659017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-737483732635187165047565013508070319000000000000)
      constant := (8306856510204174489996269604072852749689114978153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33527587616371375873/10000000000000000000)
  centralHi := (335275876163713758731/100000000000000000000)
  directionLo := (10593146701436223509/3125000000000000000)
  directionHi := (338980694445959152289/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree047.table
  base := (504945141003517257096414891249608486881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-751490535501631737575580987685796694000000000000)
      constant := (8632102746914957925353162559624835510243025264645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree047.table
  base := (63012788361573446717801722812822633327/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-753525652772322027265258095347331069000000000000)
      constant := (8678514856280040207887816459305305874995758277720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10593146701436223509/3125000000000000000)
  centralHi := (338980694445959152289/100000000000000000000)
  directionLo := (342645457108048523419/100000000000000000000)
  directionHi := (17132272855402426171/5000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree048.table
  base := (5805414408657370561657734433088236164861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1534978310542610208535923581277283638000000000000)
      constant := (18019281325435100170430760663110657064994500334749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree048.table
  base := (1449411069835158029005787941175120472957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-769567572909456889482951177186591819000000000000)
      constant := (9058060892078769105987330240857189546361311687226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342645457108048523419/100000000000000000000)
  centralHi := (17132272855402426171/5000000000000000000)
  directionLo := (173135717968955151331/50000000000000000000)
  directionHi := (346271435937910302663/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree049.table
  base := (6567227597836288293115070837028259413069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13714728632702256180542210554500000000000000)
      linear := (-652634548139090771312238728522688000000000000)
      constant := (7825920537651578515280449406818504642817566221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree049.table
  base := (6560067386249961108760340546031778208967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13714728632702256180542210554500000000000000)
      linear := (-654401910076294670304576642253938000000000000)
      constant := (7867961300539557396875562430270075001168170503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173135717968955151331/50000000000000000000)
  centralHi := (346271435937910302663/100000000000000000000)
  directionLo := (349859836815003841037/100000000000000000000)
  directionHi := (174929918407501920519/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree050.table
  base := (7334322379861151472668143718366442074757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1598972789621303675305446793088664138000000000000)
      constant := (19576454305032933903536488459774449158208814059813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree050.table
  base := (1831931739611140702952474392580785651367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-801651413183726613918337340865113319000000000000)
      constant := (9840788417106179767267649863699705698754205518606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349859836815003841037/100000000000000000000)
  centralHi := (174929918407501920519/50000000000000000000)
  directionLo := (353411804395297349977/100000000000000000000)
  directionHi := (176705902197648674989/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree051.table
  base := (4053092704104974723570234292448551605093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-815485014580325204345104199497177194000000000000)
      constant := (10189263505406841487055571562684268314722620408837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree051.table
  base := (1012514082115059604806708988198982998933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-817693333320861476136030422704374069000000000000)
      constant := (10243957754967576682876945125254741618878969573588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353411804395297349977/100000000000000000000)
  centralHi := (176705902197648674989/50000000000000000000)
  directionLo := (35692842637657583129/10000000000000000000)
  directionHi := (356928426376575831291/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree052.table
  base := (8882353218766754318664786720353507043153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1662967268699997142074970004900044638000000000000)
      constant := (21196242858121673122728252700088981786793432811377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree052.table
  base := (8876763867056156584715294653476247029397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1667470506915992676707447009087269638000000000000)
      constant := (21309980704014797912629647378838456453927330891573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35692842637657583129/10000000000000000000)
  centralHi := (356928426376575831291/100000000000000000000)
  directionLo := (360410737389131501873/100000000000000000000)
  directionHi := (180205368694565750937/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree053.table
  base := (9662407382724653859624454137535708418771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1694964508239343875459731610805734888000000000000)
      constant := (22029592394227961535991519531071154784459831429939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree053.table
  base := (9657264853793482540370183003747392095157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1699554347190262401142833172765791138000000000000)
      constant := (22147763024576853581784011970099204682548220643413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360410737389131501873/100000000000000000000)
  centralHi := (180205368694565750937/50000000000000000000)
  directionLo := (363859722551282543323/100000000000000000000)
  directionHi := (90964930637820635831/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree054.table
  base := (10445970130481790276034335126994918770917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1726961747778690608844493216711425138000000000000)
      constant := (22878567084936072718060305271636676654908054885253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree054.table
  base := (10441240388864610394998346516656574843391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1731638187464532125578219336444312638000000000000)
      constant := (23001253994836144447989687226487450534196219671519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363859722551282543323/100000000000000000000)
  centralHi := (90964930637820635831/25000000000000000000)
  directionLo := (36727632072434932369/10000000000000000000)
  directionHi := (367276320724349323691/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree055.table
  base := (2246540080152801079792785120719407796923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1758958987318037342229254822617115388000000000000)
      constant := (23743159225327692610272877383623746198824788326535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree055.table
  base := (5614175902035872631530239241005446983827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-881861013869400925006802750061417069000000000000)
      constant := (11935222981968183056603650350129732891860658611443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36727632072434932369/10000000000000000000)
  centralHi := (367276320724349323691/100000000000000000000)
  directionLo := (370661427497566715489/100000000000000000000)
  directionHi := (37066142749756671549/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree056.table
  base := (12022290273654825061713667491395603470243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-36550127078722123992122784255567462000000000000)
      constant := (502517588962881976846552217351890492419524302963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree056.table
  base := (12018293429108248708205055455565270349539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-36649099347205542335693707424517462000000000000)
      constant := (505210857683201434199214065267808139807221810099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370661427497566715489/100000000000000000000)
  centralHi := (37066142749756671549/10000000000000000000)
  directionLo := (374015897929824241229/100000000000000000000)
  directionHi := (37401589792982424123/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree057.table
  base := (12814461750228549301660506714245336146721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1822953466396730808998778034428495888000000000000)
      constant := (25519168706220413005497931993251655826848599431489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree057.table
  base := (1281078937645411744908138624505904436317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-913944854143670649442188913739938569000000000000)
      constant := (12827952974940104776921614861598134221369886369265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374015897929824241229/100000000000000000000)
  centralHi := (37401589792982424123/10000000000000000000)
  directionLo := (188670274536008654901/50000000000000000000)
  directionHi := (377340549072017309803/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree058.table
  base := (3402240961276769347502958355330789946639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-927475352968038771191769820167093069000000000000)
      constant := (13215287048216172744178218502188689249323262337502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree058.table
  base := (13605590639529396700665050134361138511067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1859973548561611023319763991158398638000000000000)
      constant := (26572162108836495129684442521862570943353761196603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188670274536008654901/50000000000000000000)
  centralHi := (377340549072017309803/100000000000000000000)
  directionLo := (76127232458218340711/20000000000000000000)
  directionHi := (95159040572772925889/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree059.table
  base := (2881113992306743330432890238157334788583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1886947945475424275768301246239876388000000000000)
      constant := (27357572910767644499034378801825192678874458251235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree059.table
  base := (14402472473583920960196230782204846944061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1892057388835880747755150154836920138000000000000)
      constant := (27504095426135053311660791058317603129156904547549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76127232458218340711/20000000000000000000)
  centralHi := (95159040572772925889/25000000000000000000)
  directionLo := (95975871353627567643/25000000000000000000)
  directionHi := (383903485414510270573/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree060.table
  base := (371193250036910095215169613059527009/244140625000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-959472592507385504576531426072783319000000000000)
      constant := (14150080263801473488268605375691605419175351418880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree060.table
  base := (475038500992986711489584343123343284737/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-962070614555075236095268159257720819000000000000)
      constant := (14225850659630524123918095143217421970089330074128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95975871353627567643/25000000000000000000)
  centralHi := (383903485414510270573/100000000000000000000)
  directionLo := (387143234711815541961/100000000000000000000)
  directionHi := (193571617355907770981/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree061.table
  base := (16004295826223749097131287514740937296031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1950942424554117742537824458051256888000000000000)
      constant := (29258332774405600177819987673170128808873071985279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree061.table
  base := (16001686231573318390461135536439378485807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1956225069384420196625922482193963138000000000000)
      constant := (29414975652195373476831769936829192245327272309263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387143234711815541961/100000000000000000000)
  centralHi := (193571617355907770981/50000000000000000000)
  directionLo := (195178048364081338783/50000000000000000000)
  directionHi := (390356096728162677567/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree062.table
  base := (8403032062176740187176382528040539643357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-991469832046732237961293031978473569000000000000)
      constant := (15116042942047562119307725992252248136447934777213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree062.table
  base := (16803669829043761302084422163429432613339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-1988308909658689921061308645872484638000000000000)
      constant := (30393914691910842577862964053794669089032834869051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195178048364081338783/50000000000000000000)
  centralHi := (390356096728162677567/100000000000000000000)
  directionLo := (78708545996623643631/20000000000000000000)
  directionHi := (98385682495779554539/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree063.table
  base := (17609229868111447253729040426157489264519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-41121161298628800189945870813523212000000000000)
      constant := (637171764400919382345151163442880449758003104279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree063.table
  base := (1100439605047910666281908439482756969991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-20616252550336322913231579689295981000000000000)
      constant := (320290970092929637968495583211956736049612965048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78708545996623643631/20000000000000000000)
  centralHi := (98385682495779554539/25000000000000000000)
  directionLo := (79340753309326296887/20000000000000000000)
  directionHi := (99175941636657871109/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree064.table
  base := (4603414284680502095164866912993711862877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1023467071586078971346054637884163819000000000000)
      constant := (16113160709256546441944148680589157539275322145786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree064.table
  base := (9205821587548735211169573264277617010203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1026238295103614684966040486614763819000000000000)
      constant := (16199386871385645980542819024028735440376049064827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79340753309326296887/20000000000000000000)
  centralHi := (99175941636657871109/25000000000000000000)
  directionLo := (199919906751430766307/50000000000000000000)
  directionHi := (79967962700572306523/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree065.table
  base := (9609611612453593983723785977039908853367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1039465691355752338038435440837008944000000000000)
      constant := (16623399000263834266510744945462556031140593577303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree065.table
  base := (19217376816278775932722827376443877185359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2084560430481499094367467136908049138000000000000)
      constant := (33424687968191649582525356565217411487489339837231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199919906751430766307/50000000000000000000)
  centralHi := (79967962700572306523/20000000000000000000)
  directionLo := (201475727155730778051/50000000000000000000)
  directionHi := (402951454311461556103/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree066.table
  base := (20025817339499910081068204040203720360443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2110928622250851409461632487579708138000000000000)
      constant := (34282843698894888185405330053053547616496251056987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree066.table
  base := (10012062473252526491236240046617621494313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1058322135377884409401426650293285319000000000000)
      constant := (17233127634043853950381511961165172785736618431817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201475727155730778051/50000000000000000000)
  centralHi := (402951454311461556103/100000000000000000000)
  directionLo := (406039250074965890847/100000000000000000000)
  directionHi := (12688726564842684089/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree067.table
  base := (5208334865191169343172137982848431278471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1071462930895099071423197046742699194000000000000)
      constant := (17667228127011412512406429826325895270670639734478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree067.table
  base := (5207947148125624557583423180767834175917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1074364055515019271619119732132546069000000000000)
      constant := (17761736703276673832526065813805888785557297060506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406039250074965890847/100000000000000000000)
  centralHi := (12688726564842684089/3125000000000000000)
  directionLo := (409103740720076386961/100000000000000000000)
  directionHi := (204551870360038193481/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree068.table
  base := (21641699286307846352326994956411553757273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2174923101329544876231155699391088638000000000000)
      constant := (36401633625889291529619112487301310852634538158457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree068.table
  base := (10820139212245135440065873393948024064097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1090405975652154133836812813971806819000000000000)
      constant := (18298170182769342966469364725175737799164231903873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409103740720076386961/100000000000000000000)
  centralHi := (204551870360038193481/50000000000000000000)
  directionLo := (206072723049945577221/50000000000000000000)
  directionHi := (412145446099891154443/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree069.table
  base := (22450815288637140380787459826020479542653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2206920340868891609615917305296778888000000000000)
      constant := (37484373972705975930837520312560302053282389806877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree069.table
  base := (2806189227071754746015594357043148621877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1106447895789288996054505895811067569000000000000)
      constant := (18842427161811709097694963868955252196620643615572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206072723049945577221/50000000000000000000)
  centralHi := (412145446099891154443/100000000000000000000)
  directionLo := (207582433511723893121/50000000000000000000)
  directionHi := (415164867023447786243/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree070.table
  base := (23260613862493114772818215211921689643777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-45692195518535476387768957371478962000000000000)
      constant := (787401543503179585025480797933175177715056591857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree070.table
  base := (23259421998688859887015796765913833591339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-45815910854139749317232611332666462000000000000)
      constant := (791612523201190866758220924514804769752784523899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207582433511723893121/50000000000000000000)
  centralHi := (415164867023447786243/100000000000000000000)
  directionLo := (104540621554588733891/25000000000000000000)
  directionHi := (83632497243670987113/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree071.table
  base := (6017757138758765855855188977363477229943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1135457409973792538192720258554079694000000000000)
      constant := (19848268550751020134333926334866053054120874764974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree071.table
  base := (19255949832937167908662353107177874517/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1138531736063558720489892059489589069000000000000)
      constant := (19954408410736812279088305765143323603884011033125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104540621554588733891/25000000000000000000)
  centralHi := (83632497243670987113/20000000000000000000)
  directionLo := (26321173076984486249/6250000000000000000)
  directionHi := (84227753846350355997/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree072.table
  base := (24881999370830370547105718481278158030451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2302912059486931809770202123013849638000000000000)
      constant := (40825957026887339555991868746762673435569340815059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree072.table
  base := (24881000413911018998860992611182263624897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2309147312401387165415170282657699638000000000000)
      constant := (41044262538271717424209782603712224954190420751073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26321173076984486249/6250000000000000000)
  centralHi := (84227753846350355997/20000000000000000000)
  directionLo := (106023541318589204993/25000000000000000000)
  directionHi := (424094165274356819973/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree073.table
  base := (12846736072189313255326111211928552257361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1167454649513139271577481864459769944000000000000)
      constant := (20985467092079195142346413859686974640278012667249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree073.table
  base := (25692557862812057174114662965062927427973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2341231152675656889850556446336221138000000000000)
      constant := (42195349578541128542538279558982858853091684894757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106023541318589204993/25000000000000000000)
  centralHi := (424094165274356819973/100000000000000000000)
  directionLo := (427029108011939013227/100000000000000000000)
  directionHi := (106757277002984753307/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree074.table
  base := (662634949340203121356403033033019025701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1183453269282812638269862667412615069000000000000)
      constant := (21565733734284025207745967988823848508135650446180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree074.table
  base := (26504561347010952676120126465337988034407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2373314992949926614285942610014742638000000000000)
      constant := (43362076851342523216763530529158692137727180846663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427029108011939013227/100000000000000000000)
  centralHi := (106757277002984753307/25000000000000000000)
  directionLo := (13435750509629989919/3125000000000000000)
  directionHi := (429944016308159677409/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree075.table
  base := (27317732708420024962007711284682544828219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2398903778104972009924486940730920388000000000000)
      constant := (44307555882721039689145611857840485751107198882971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree075.table
  base := (13658483640463330834805917319011294648431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1202699416612098169360664386846632069000000000000)
      constant := (22272221686016823907686828495636998328504356556879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13435750509629989919/3125000000000000000)
  centralHi := (429944016308159677409/100000000000000000000)
  directionLo := (432839294922387878327/100000000000000000000)
  directionHi := (54104911865298484791/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree076.table
  base := (1125217459557246810087951388302468049109/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2430901017644318743309248546636610638000000000000)
      constant := (45499198526142378976368076006542699398490846524525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree076.table
  base := (14064868162901474631190976887673417598717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1218741336749233031578357468685892819000000000000)
      constant := (22871224125956153093556338872083019660033374135453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432839294922387878327/100000000000000000000)
  centralHi := (54104911865298484791/12500000000000000000)
  directionLo := (43571533516578076857/10000000000000000000)
  directionHi := (435715335165780768571/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree077.table
  base := (28943473328586316006836338398979329967153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-50263229738442152585592043929434712000000000000)
      constant := (953191726242030099280366245443467447017386186273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree077.table
  base := (14471416487959999186773771618931756795827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-25199658303803426404001031643370481000000000000)
      constant := (479143782539474106049265434162271453084904875907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43571533516578076857/10000000000000000000)
  centralHi := (435715335165780768571/100000000000000000000)
  directionLo := (109643128879659927587/25000000000000000000)
  directionHi := (438572515518639710349/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree078.table
  base := (29756810737779779811806217326075148604989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2494895496723012210078771758447991138000000000000)
      constant := (47929143327899352976386827315027360330811643943901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree078.table
  base := (29756225185123098736014005220631443092937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2501650354047005512027487264728828638000000000000)
      constant := (48185369958947146957483334939620879430595527603433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109643128879659927587/25000000000000000000)
  centralHi := (438572515518639710349/100000000000000000000)
  directionLo := (441411202211799636003/100000000000000000000)
  directionHi := (110352800552949909001/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree079.table
  base := (15285209692025094306192678451466696314693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1263446368131179471731766682176840694000000000000)
      constant := (24583722044806057220241556813433530685020496395237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree079.table
  base := (3056988402974017682596455940701238773891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1266867097160637618231436714203675069000000000000)
      constant := (24715142704366711877526719160418336583260602730095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441411202211799636003/100000000000000000000)
  centralHi := (110352800552949909001/25000000000000000000)
  directionLo := (222115874887290004667/50000000000000000000)
  directionHi := (88846349954916001867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree080.table
  base := (31384272785294490317952752524849394754369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2558889975801705676848294970259371638000000000000)
      constant := (50421296272740330868320117031635083440540502868321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree080.table
  base := (31383783404342668747276102104452622814709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2565818034595544960898259592085871638000000000000)
      constant := (50690836448479321149703930590923569182080696351381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222115874887290004667/50000000000000000000)
  centralHi := (88846349954916001867/20000000000000000000)
  directionLo := (447034501551618344973/100000000000000000000)
  directionHi := (223517250775809172487/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree081.table
  base := (8049586758198181225493664787772391255237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1295443607670526205116528288082530944000000000000)
      constant := (25845349668580947232229386728156254322472160728266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree081.table
  base := (32197899747149687727827054712138566665677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2597901874869814685333645755764393138000000000000)
      constant := (51967022545900435072337832218616380446791409098093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447034501551618344973/100000000000000000000)
  centralHi := (223517250775809172487/50000000000000000000)
  directionLo := (449819790190719224191/100000000000000000000)
  directionHi := (3514217110864993939/781250000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree082.table
  base := (16506310270573410765889437510797276393999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1311442227440199571808909091035376069000000000000)
      constant := (26487826397620441571067773848444010176192318954991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree082.table
  base := (8253052948046807331096351663415300670007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1314992857572042204884515959721457319000000000000)
      constant := (26629421610288477697406024431947677839347668334126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449819790190719224191/100000000000000000000)
  centralHi := (3514217110864993939/781250000000000000)
  directionLo := (113146984525920271289/25000000000000000000)
  directionHi := (452587938103681085157/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree083.table
  base := (16913536911259082497532525283487246106357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1327440847209872938501289893988221194000000000000)
      constant := (27138078103363679677270912822768192989548925944213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree083.table
  base := (33826700345595570088562264598721858904953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2662069555418354134204418083121436138000000000000)
      constant := (54566298038900224359966516002035677607018523367577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113146984525920271289/25000000000000000000)
  centralHi := (452587938103681085157/100000000000000000000)
  directionLo := (45533925790190796967/10000000000000000000)
  directionHi := (455339257901907969671/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree084.table
  base := (8660422320700700076938934198789357895777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-27417131979174414391707565243695231000000000000)
      constant := (567267440552579207221395089748782317707253847714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree084.table
  base := (34641348083732009204134800372683456234969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (672021703002410552846568317170500000000000000)
      linear := (-54982722361073956298771515240815462000000000000)
      constant := (1140599726724728036752604823994666661346026342729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45533925790190796967/10000000000000000000)
  centralHi := (455339257901907969671/100000000000000000000)
  directionLo := (91614810561694457439/20000000000000000000)
  directionHi := (114518513202118071799/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree085.table
  base := (35456451037612576590898423233963230821571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2718876173498439343772102999787822888000000000000)
      constant := (56923811338672736325600453071771248026909187855139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree085.table
  base := (17728069685472674481799472499181670653171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1363118617983446791537595205239239569000000000000)
      constant := (28614054289593083394637203097602083979360821939539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91614810561694457439/20000000000000000000)
  centralHi := (114518513202118071799/25000000000000000000)
  directionLo := (115198154262041525127/25000000000000000000)
  directionHi := (460792617048166100509/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree086.table
  base := (36271344746137669546281722458233272024101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2750873413037786077156864605693513138000000000000)
      constant := (58270962376313917600243716337483883490395913907909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree086.table
  base := (18135530047552710058352889597952611517403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1379160538120581653755288287078500319000000000000)
      constant := (29291231814558221831226464436370337637363154829627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115198154262041525127/25000000000000000000)
  centralHi := (460792617048166100509/100000000000000000000)
  directionLo := (463495236216961192529/100000000000000000000)
  directionHi := (46349523621696119253/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree087.table
  base := (37086357461152932441304098062784315293279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2782870652577132810541626211599203388000000000000)
      constant := (59633661994585426316763986690175251306599303528511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree087.table
  base := (37086097519157708373949088219861672840943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2790404916515433031945962737835522138000000000000)
      constant := (59952451471559591254608340905477852785904798881487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463495236216961192529/100000000000000000000)
  centralHi := (46349523621696119253/10000000000000000000)
  directionLo := (116545546908047781441/25000000000000000000)
  directionHi := (93236437526438225153/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree088.table
  base := (18950738746799682117700806606432089479251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1407433946058239771963193908752446819000000000000)
      constant := (30505954964709812690561437433868016713314564654259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree088.table
  base := (37901240147141692921479722358077255226113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2822488756789702756381348901514043638000000000000)
      constant := (61338071846810261976390288827626049639508415818017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116545546908047781441/25000000000000000000)
  centralHi := (93236437526438225153/20000000000000000000)
  directionLo := (18754149626586826437/4000000000000000000)
  directionHi := (234426870332335330463/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree089.table
  base := (38716694290324416100729671735143685023747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2846865131655826277311149423410583888000000000000)
      constant := (62405705942410150584377604147413184830414633690723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree089.table
  base := (3871647760326363955814624868192056725933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1427286298531986240408367532596282569000000000000)
      constant := (31369662260234403098158476403765828727120314681985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18754149626586826437/4000000000000000000)
  centralHi := (234426870332335330463/50000000000000000000)
  directionLo := (471510157053878373007/100000000000000000000)
  directionHi := (29469384815867398313/6250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree090.table
  base := (19765999161851239144343659295527108951533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1439431185597586505347955514658137069000000000000)
      constant := (31907524909159163014033521308260903288068062566797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree090.table
  base := (39531800522751900123750096520295163900707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2886656437338242205252121228871086638000000000000)
      constant := (64156209280975583327856453493376800400337346943363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471510157053878373007/100000000000000000000)
  centralHi := (29469384815867398313/6250000000000000000)
  directionLo := (474151691207246299261/100000000000000000000)
  directionHi := (237075845603623149631/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree091.table
  base := (10086845247995284336341662824174849405329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-29702649089127752490619108522673106000000000000)
      constant := (665713687375733525755941181274255848864364574978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree091.table
  base := (20173600226673350234728700882902742295537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (336010851501205276423284158585250000000000000)
      linear := (-29783064057270529894770483597444981000000000000)
      constant := (669272713646790987172188956342923759210676674017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474151691207246299261/100000000000000000000)
  centralHi := (237075845603623149631/50000000000000000000)
  directionLo := (119194647621131316323/25000000000000000000)
  directionHi := (476778590484525265293/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree092.table
  base := (5145354316163871062933576777999851999647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1471428425136933238732717120563827319000000000000)
      constant := (33340190200241227412430153860546759757090773495292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree092.table
  base := (5145333720798531853981492229660708999613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1475412058943390827061446778114064819000000000000)
      constant := (33518437158679742281625868823389842173826553118068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119194647621131316323/25000000000000000000)
  centralHi := (476778590484525265293/100000000000000000000)
  directionLo := (239695547734062764001/50000000000000000000)
  directionHi := (479391095468125528003/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree093.table
  base := (41978351924517902831756488562434503393359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-2974854089813213210850195847033344888000000000000)
      constant := (68136366772910537438609069389392264805819903709231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree093.table
  base := (4197820157656800161256956978653956605529/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1491453979080525689279139859953325569000000000000)
      constant := (34250327132675709553071207355502177124805575443805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239695547734062764001/50000000000000000000)
  centralHi := (479391095468125528003/100000000000000000000)
  directionLo := (240994720110134488843/50000000000000000000)
  directionHi := (481989440220268977687/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree094.table
  base := (21396963423884321283286221140080645826859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1503425664676279972117478726469517569000000000000)
      constant := (34803950168554406183525023406710703291600384110731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree094.table
  base := (8558757933899775221467783598136034359749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-3014991798435321102993665883585172638000000000000)
      constant := (69980065640972046263328771838777481399226994483705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240994720110134488843/50000000000000000000)
  centralHi := (481989440220268977687/100000000000000000000)
  directionLo := (242286926263865422357/50000000000000000000)
  directionHi := (96914770505546168943/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree095.table
  base := (43609553584362147225760339396701803569053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-3038848568891906677619719058844725388000000000000)
      constant := (71094980963976416972341486385840756593494708444477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree095.table
  base := (8721885687268555616401329852681721478231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-3047075638709590827429052047263694138000000000000)
      constant := (71475108317512054032878148972707389080251049125395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242286926263865422357/50000000000000000000)
  centralHi := (96914770505546168943/20000000000000000000)
  directionLo := (487144554134895198943/100000000000000000000)
  directionHi := (15223267316715474967/3125000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree096.table
  base := (44425226974954740938064684269065994022487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32929063447118117089481847541354500000000000000)
      linear := (-3070845808431253411004480664750415638000000000000)
      constant := (72597608536958571838782772363280065940555950019383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree096.table
  base := (5553139101850952661071936712605585326593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16464531723559058544740923770677250000000000000)
      linear := (-1539579739491930275932219105471107819000000000000)
      constant := (36492891090304578166866631778210045390253321609348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487144554134895198943/100000000000000000000)
  centralHi := (15223267316715474967/3125000000000000000)
  directionLo := (244850880482899549127/50000000000000000000)
  directionHi := (97940352193159819651/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree097.table
  base := (45240942361593677346140719854084022955709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (163268)
      previous := (81634)
      next := (81634)
      square := (3499741040186854829363571850500000000000000)
      linear := (-329773944943203331319932221347232000000000000)
      constant := (7877115841303796848957425031700953489116657309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree097.table
  base := (45240838235893348798940779802989060947613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (163268)
      previous := (81634)
      next := (81634)
      square := (3499741040186854829363571850500000000000000)
      linear := (-330666736024883651429463744778482000000000000)
      constant := (7919235532686261213607268636743230735335218813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell051.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244850880482899549127/50000000000000000000)
  centralHi := (97940352193159819651/20000000000000000000)
  directionLo := (246122841667897331549/50000000000000000000)
  directionHi := (492245683335794663099/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree098.table
  base := (46056695538994746156490859198042837569051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13714728632702256180542210554500000000000000)
      linear := (-1305639436697187371001251093944938000000000000)
      constant := (31507498588330429683138737624937009058687200859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree098.table
  base := (23028300287913383542454968618766467835097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6857364316351128090271105277250000000000000)
      linear := (-654587080285797584492963460703719000000000000)
      constant := (15837988976188980212248352770239060695860427673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell051.Kernel098
