import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell150.Parameters
import ForestUnimodality.BinomialMassData.Q28_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q28_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q28_53.Batch100_149
import ForestUnimodality.BinomialMassData.Q28_53.Batch150_199
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree000.table
  base := (175883201017276425173179179/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78732540757351174992573206250000000000)
      linear := (-5720676555117492614530028125000000000)
      constant := (109927000635797765733236986875000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree000.table
  base := (175883201017276425173179179/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78732540757351174992573206250000000000)
      linear := (-5720676555117492614530028125000000000)
      constant := (109927000635797765733236986875000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree001.table
  base := (479023898608104949727980002280450296700063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-1997980491289146593057377001225000000000000)
      constant := (1346139857557859265227768946049284883430476967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree001.table
  base := (239459628511257278076080833890025839288113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-15111432866768755869297069356951821875000000000)
      constant := (10176616010422261300928685840333295329165028063291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1996761977086751159/4000000000000000000)
  directionHi := (1559970294599024343/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree002.table
  base := (277908336630426576662259762927228222538643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-3867405939031692892081035210425000000000000)
      constant := (782755591321513389867140751648784077111048187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree002.table
  base := (69450868099761060912415456323937433588393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-14625398385879946807629087034003303125000000000)
      constant := (2958293578523009061014291223418925466480951455251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/4000000000000000000)
  centralHi := (1559970294599024343/3125000000000000000)
  directionLo := (70596196720674968671/100000000000000000000)
  directionHi := (2206131147521092771/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree003.table
  base := (173996499242768713683719389071292634711679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-5736831386774239191104693419625000000000000)
      constant := (493404208449795340480507637729361010905106311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree003.table
  base := (10869724033510664000102370268347204920049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-3615846723062585946768273231588449218750000000)
      constant := (310764607315162408181634321746043212098277219062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70596196720674968671/100000000000000000000)
  centralHi := (2206131147521092771/3125000000000000000)
  directionLo := (43231164936699192541/50000000000000000000)
  directionHi := (86462329873398385083/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree004.table
  base := (117970702377385474161208246005435050726741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-7606256834516785490128351628825000000000000)
      constant := (339552334396406921520967471398467057491415469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree004.table
  base := (117912969308825963970694577590029935449139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-115059049163484338214360766980232350000000000000)
      constant := (5132661115716798541498240758340832106181697433473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43231164936699192541/50000000000000000000)
  centralHi := (86462329873398385083/100000000000000000000)
  directionLo := (1996761977086751159/2000000000000000000)
  directionHi := (99838098854337557951/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree005.table
  base := (21479870781788081525581938108983315491233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-2368920570564832947288002459506250000000000)
      constant := (63508167463808830655468159450509133214873497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree005.table
  base := (42939342984142781165152438783354846119027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-71668888486733306853141488201170959375000000000)
      constant := (1920051082827976783973915559104286554804968056689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/2000000000000000000)
  centralHi := (99838098854337557951/100000000000000000000)
  directionLo := (55811193945660663499/50000000000000000000)
  directionHi := (111622387891321326999/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree006.table
  base := (16545672831369565215110360119607585418723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-2836276932500469522043917011806250000000000)
      constant := (51022963252081600123705324663227707441192907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree006.table
  base := (4134565736233109223903428524610290758589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-7150687699310370383258549409352145312500000000)
      constant := (128556853806128194870787998125641514768548133082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55811193945660663499/50000000000000000000)
  centralHi := (111622387891321326999/100000000000000000000)
  directionLo := (30569049885334101599/25000000000000000000)
  directionHi := (122276199541336406397/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree007.table
  base := (26510419715632035718257706587662173368147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-6607266588872212193599663128212500000000000)
      constant := (86803831676366241339763618698593044991124923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree007.table
  base := (26499136836490963621366237547102232884931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-99947616296715582345063697623280528125000000000)
      constant := (1312351867053989820040635128057495232514410290017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30569049885334101599/25000000000000000000)
  centralHi := (122276199541336406397/100000000000000000000)
  directionLo := (132073390469029896871/100000000000000000000)
  directionHi := (16509173808628737109/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree008.table
  base := (1742607043320272374586970739065794023273/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-15083958625486970686222984465625000000000000)
      constant := (154521778313991786935346449676495385284346425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree008.table
  base := (5443388288787154687748361676555020589197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-28521745050426680022756200583583828125000000000)
      constant := (292039732287234300779528385996740809899527282879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132073390469029896871/100000000000000000000)
  centralHi := (16509173808628737109/12500000000000000000)
  directionLo := (141192393441349937343/100000000000000000000)
  directionHi := (2206131147521092771/1562500000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree009.table
  base := (9086653914590164998242159584424670269143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-4238346018307379246311660668706250000000000)
      constant := (35676884094733729976238290163323898786022687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree009.table
  base := (18165754756985934006569963211584934525037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-42742114702232619278995302348463365625000000000)
      constant := (359640628811922169331342531054270568326114901253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141192393441349937343/100000000000000000000)
  centralHi := (2206131147521092771/1562500000000000000)
  directionLo := (5990285931260253477/4000000000000000000)
  directionHi := (74878574140753168463/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree010.table
  base := (7646178827148933389557742112302719483073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-4705702380243015821067575221006250000000000)
      constant := (33993168396369905310902427568208339027952057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree010.table
  base := (30571689758401594019884706645532669635043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-284731416023377991165894023512889762500000000000)
      constant := (2056155453505970520346887373001297040378881606801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5990285931260253477/4000000000000000000)
  centralHi := (74878574140753168463/50000000000000000000)
  directionLo := (157857894820376962999/100000000000000000000)
  directionHi := (157857894820376963/100000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree011.table
  base := (12921438311284141134216645767755456131677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-10346117484357304791646979546612500000000000)
      constant := (66545392498361551701754769228875076273880693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree011.table
  base := (12915712981084028119393061228219003322769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-156505071916680133328908116467499665625000000000)
      constant := (1006361003749223368922121702325233741135130513883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157857894820376962999/100000000000000000000)
  centralHi := (157857894820376963/100000000000000000)
  directionLo := (165562756841124494497/100000000000000000000)
  directionHi := (82781378420562247249/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree012.table
  base := (68313263210483490804825336563661550171/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-2820207552057144485289702162803125000000000)
      constant := (16666140983765375587271270249943011777213560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree012.table
  base := (10925035984992513709785860445704834849901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-56881478607223757024956407059518150000000000000)
      constant := (336078509004133667461888931868088721529187793269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165562756841124494497/100000000000000000000)
  centralHi := (82781378420562247249/50000000000000000000)
  directionLo := (34584931949359354033/20000000000000000000)
  directionHi := (86462329873398385083/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree013.table
  base := (18469029136346021358630618205025323290019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-24431085864199702181341275511625000000000000)
      constant := (136216382942294597591077349241016133121663371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree013.table
  base := (2307493830515066903113251792435122582511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-46195949931665602205207581472402308593750000000)
      constant := (257534947907734163266021423733676041712021300577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34584931949359354033/20000000000000000000)
  centralHi := (86462329873398385083/50000000000000000000)
  directionLo := (17998569233207831513/10000000000000000000)
  directionHi := (179985692332078315131/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree014.table
  base := (7776631838378043130785544586111249658507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-13150255655971124240182466860412500000000000)
      constant := (70713398510190851076849574860486500290746163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree014.table
  base := (7772576222821839902434141626506858064279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-198923163631653546566791430600664018750000000000)
      constant := (1069611849614869889161950362222306556656985509453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17998569233207831513/10000000000000000000)
  centralHi := (179985692332078315131/100000000000000000000)
  directionLo := (186779980029899549201/100000000000000000000)
  directionHi := (93389990014949774601/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree015.table
  base := (6513877965732995822533259423283843348923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-14084968379842397389694295965012500000000000)
      constant := (74360533004598635882653333754254315967124707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree015.table
  base := (13020515217539454055480184853805487255647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-142041685024429789541835023541145868750000000000)
      constant := (749895223440396770990973292232106880362620224343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186779980029899549201/100000000000000000000)
  centralHi := (93389990014949774601/50000000000000000000)
  directionLo := (38667129417985914929/20000000000000000000)
  directionHi := (96667823544964787323/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree016.table
  base := (169171504724084276688816093984539038539/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-3754920275928417634801531267403125000000000)
      constant := (19739389658447741836099889039020561274048408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree016.table
  base := (2164104960861811099588975172666824382319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-454403782883271644117427280045547175000000000000)
      constant := (2388882421994958942883082194153366834204364778665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38667129417985914929/20000000000000000000)
  centralHi := (96667823544964787323/50000000000000000000)
  directionLo := (1996761977086751159/1000000000000000000)
  directionHi := (199676197708675115901/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree017.table
  base := (8898895451113391030337415980748312340983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-31908787655169887377435908348425000000000000)
      constant := (168862800384338346834590844120622009365821247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree017.table
  base := (138955632515114379931492985441705014469/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-60335313836656739951168686183457092968750000000)
      constant := (319325510934896042705647043927903616167800833764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/1000000000000000000)
  centralHi := (199676197708675115901/100000000000000000000)
  directionLo := (51455378379661411983/25000000000000000000)
  directionHi := (205821513518645647933/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree018.table
  base := (900168140371142018366914541715285956879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-4222276637864054209557445819703125000000000)
      constant := (22680708091462152459225464617753238252873111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree018.table
  base := (3598129798923973482249703103235966277719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-85160206417206032516878616481627718750000000000)
      constant := (457509929339921773142584203183083390698926974511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51455378379661411983/25000000000000000000)
  centralHi := (205821513518645647933/100000000000000000000)
  directionLo := (42357718032404981203/20000000000000000000)
  directionHi := (6618393442563278313/3125000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree019.table
  base := (2849853966729177519709936973408455867109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-17823819275327489987741612383412500000000000)
      constant := (97783235038368866744294524153154352530709181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree019.table
  base := (5695209213035214004015471968758062793103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-539239966313218470593193908311875881250000000000)
      constant := (2958778512354704436447418846373584016812289043221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42357718032404981203/20000000000000000000)
  centralHi := (6618393442563278313/3125000000000000000)
  directionLo := (43518418362128131187/20000000000000000000)
  directionHi := (3399876434541260249/1562500000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree020.table
  base := (1091335310424697612040754372967410137829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-9379265999599381568626720744006250000000000)
      constant := (52786189810305406909162896463165455077161661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree020.table
  base := (4361370784180162900029922494290195574621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-567518694123200746085116117733985450000000000000)
      constant := (3194544316625965004968935504830399316264056412847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43518418362128131187/20000000000000000000)
  centralHi := (3399876434541260249/1562500000000000000)
  directionLo := (223244775782642653997/100000000000000000000)
  directionHi := (111622387891321326999/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree021.table
  base := (1587216177391548610788251067019370984343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-19693244723070036286765270592612500000000000)
      constant := (114056821185386084793589974920007413095019487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree021.table
  base := (792733920110915000135813169249290920103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-49649785161098585131419860596341251562500000000)
      constant := (287612132178690842620196221151162856748277102407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223244775782642653997/100000000000000000000)
  centralHi := (111622387891321326999/50000000000000000000)
  directionLo := (2287578226202428943/1000000000000000000)
  directionHi := (228757822620242894301/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree022.table
  base := (1053562959311742045144417550392927451733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-20627957446941309436277099697212500000000000)
      constant := (123208672887878376832254808535153733211917997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree022.table
  base := (1052026321021757182842017879652224481097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-312038074871582648534480268289102293750000000000)
      constant := (1864169514664771787585565784924558644869187476179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2287578226202428943/1000000000000000000)
  centralHi := (228757822620242894301/100000000000000000000)
  directionLo := (234141096148597184291/100000000000000000000)
  directionHi := (58535274037149296073/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree023.table
  base := (71677242436783888477364304444985544873/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-5390667542703145646447232200453125000000000)
      constant := (33251159903729919055104812849634428791096514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree023.table
  base := (57206985507175606409968589426529235339/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-163088719388286893140220686500078539062500000000)
      constant := (1006205059040827475278483091431425906765349559365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234141096148597184291/100000000000000000000)
  centralHi := (58535274037149296073/25000000000000000000)
  directionLo := (14962709428538861569/6250000000000000000)
  directionHi := (47880670171324357021/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree024.table
  base := (279690766854803123044706478361598043751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-44994765789367711470601515812825000000000000)
      constant := (286850477776533042971074822520917728904896559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree024.table
  base := (277329449107815958782663408043862149843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-226877868454376616017601651807474575000000000000)
      constant := (1446733370316329617384095609096379497454480203467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14962709428538861569/6250000000000000000)
  centralHi := (47880670171324357021/20000000000000000000)
  directionLo := (30569049885334101599/12500000000000000000)
  directionHi := (244552399082672812793/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree025.table
  base := (-505919852789368517145049445694768491743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-46864191237110257769625174022025000000000000)
      constant := (308908327703890141614219036954543395306693913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree025.table
  base := (-507984668783811886640116539313075865127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-708912333173112123544727164844533293750000000000)
      constant := (4673985602504515174757394035371608674855878920611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30569049885334101599/12500000000000000000)
  centralHi := (244552399082672812793/100000000000000000000)
  directionLo := (1996761977086751159/800000000000000000)
  directionHi := (62398811783960973719/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree026.table
  base := (-304929863054855933356813168735616906361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-12183404171213201017162208057806250000000000)
      constant := (83038878944572226607806601301771652110031951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree026.table
  base := (-1221522387340381740572224114634753351343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-737191060983094399036649374266642862500000000000)
      constant := (5025763811184971998836277093346995819533750229099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/800000000000000000)
  centralHi := (62398811783960973719/25000000000000000000)
  directionLo := (15908637945571020723/6250000000000000000)
  directionHi := (254538207129136331569/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree027.table
  base := (-233731839055779301739306555005727424099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-6325380266574418795959061305053125000000000)
      constant := (44571144746596224786048597061201411665705909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree027.table
  base := (-467856718978259605082167844070073290899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-63789149066089722877380965307396035937500000000)
      constant := (449599067585644652626580992522090899954187123069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15908637945571020723/6250000000000000000)
  centralHi := (254538207129136331569/100000000000000000000)
  directionLo := (259386989620195155247/100000000000000000000)
  directionHi := (16211686851262197203/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree028.table
  base := (-98526142544498109847148547460493993817/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-52472467580337896666696148649625000000000000)
      constant := (382130074631562107190816220370186809284201175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree028.table
  base := (-2464522793651287335691642217917311648653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-793748516603058950020493793110862000000000000000)
      constant := (5781970687052033494198688554755659182713214692929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259386989620195155247/100000000000000000000)
  centralHi := (16211686851262197203/6250000000000000000)
  directionLo := (132073390469029896871/50000000000000000000)
  directionHi := (264146780938059793743/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree029.table
  base := (-1502670153491220700554951536168230567439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-27170946514040221482859903429412500000000000)
      constant := (204411093096207119197989550703253440336063849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree029.table
  base := (-3006531423399853513898996789767890613741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-822027244413041225512416002532971568750000000000)
      constant := (6185866396261930665442773918042170771556178653313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132073390469029896871/50000000000000000000)
  centralHi := (264146780938059793743/100000000000000000000)
  directionLo := (26882230818079713157/10000000000000000000)
  directionHi := (268822308180797131571/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree030.table
  base := (-1750607601941010425143415931506195245587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-28105659237911494632371732534012500000000000)
      constant := (218316004360630981099606269376899097555146117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree030.table
  base := (-3502250263128759451000217965729415817761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-283435324074341167001446070651693712500000000000)
      constant := (2202224046170443106272546823517882517655481038391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26882230818079713157/10000000000000000000)
  centralHi := (268822308180797131571/100000000000000000000)
  directionLo := (136708947102378405387/50000000000000000000)
  directionHi := (10936715768190272431/4000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree031.table
  base := (-790960908542862887293458550418670704369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-58080743923565535563767123277225000000000000)
      constant := (465548232373980905130709892735869769957137395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree031.table
  base := (-988925772101859359320411607919624960747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-219646175008251444124065105344297676562500000000)
      constant := (1761054245443496439232438321194830821251596716271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136708947102378405387/50000000000000000000)
  centralHi := (10936715768190272431/4000000000000000000)
  directionLo := (69484376106735186873/25000000000000000000)
  directionHi := (277937504426940747493/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree032.table
  base := (-853415258462849646938717758181070323/1953125000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-7493771171413510232848847685803125000000000)
      constant := (61945171113848887810835903887452399016123520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree032.table
  base := (-4370265427239381722488717074111223276083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-906863427842988051988182630799300275000000000000)
      constant := (7498357531908918846278341665805357010841793185919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69484376106735186873/25000000000000000000)
  centralHi := (277937504426940747493/100000000000000000000)
  directionLo := (141192393441349937343/50000000000000000000)
  directionHi := (282384786882699874687/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree033.table
  base := (-2374047120663314117633852607130586128611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-30909797409525314080907219847812500000000000)
      constant := (263331728397678633158678293133120183564731701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree033.table
  base := (-1187192382871241435131765969724568709059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-77928512971080860623342070018450820312500000000)
      constant := (664081122785095685848480274312960919770190854029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141192393441349937343/50000000000000000000)
  centralHi := (282384786882699874687/100000000000000000000)
  directionLo := (143381553344999672251/50000000000000000000)
  directionHi := (286763106689999344503/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree034.table
  base := (-5093007559269722554020687890516898891323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-63689020266793174460838097904825000000000000)
      constant := (558847814364534609408378241445738031014273693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree034.table
  base := (-2546796116575781135926499232488663261267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-481710441731476301486013524821759706250000000000)
      constant := (4227981918640973442594117176853691128143479377631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143381553344999672251/50000000000000000000)
  centralHi := (286763106689999344503/100000000000000000000)
  directionLo := (36384446980778250351/12500000000000000000)
  directionHi := (291075575846226002809/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree035.table
  base := (-5406222681438377092202496785078067671779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-65558445714535720759861756114025000000000000)
      constant := (592108833156902566982131162077215707909972789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree035.table
  base := (-5406728503141984763087216186442960671371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-991699611272934878463949259065628981250000000000)
      constant := (8959243876115913048358890276326428284372537034903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36384446980778250351/12500000000000000000)
  centralHi := (291075575846226002809/100000000000000000000)
  directionLo := (36915634888452960297/12500000000000000000)
  directionHi := (295325079107623682377/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree036.table
  base := (-1422353944527353376613564185224000993231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-16856967790569566764721353580806250000000000)
      constant := (156610451202538386751277607119205781210014121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree036.table
  base := (-5689853059194470996187566491162233084411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-339992779694305717985290489495912850000000000000)
      constant := (3159580815688148161809868720812535507482348974541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36915634888452960297/12500000000000000000)
  centralHi := (295325079107623682377/100000000000000000000)
  directionLo := (5990285931260253477/2000000000000000000)
  directionHi := (299514296563012673851/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree037.table
  base := (-2971997107791958608142304157353337928119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-34648648305010406678954536266212500000000000)
      constant := (330921388016173900266958134660344473759913729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree037.table
  base := (-5944371979745895393426941252657776157767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1048257066892899429447793677909848118750000000000)
      constant := (10014399819202661003446897472897495670348983352131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5990285931260253477/2000000000000000000)
  centralHi := (299514296563012673851/100000000000000000000)
  directionLo := (30364572340368705613/10000000000000000000)
  directionHi := (303645723403687056131/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree038.table
  base := (-6171139824481854983252153355286890556347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-71166722057763359656932730741625000000000000)
      constant := (698308427061273840935330572015599124427221277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree038.table
  base := (-1542866489151789197756682308161703356473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-269133948675720426234928971832989421875000000000)
      constant := (2641541459035956217930592412216061470425612728189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30364572340368705613/10000000000000000000)
  centralHi := (303645723403687056131/100000000000000000000)
  directionLo := (61544337460747936729/20000000000000000000)
  directionHi := (153860843651869841823/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree039.table
  base := (-6371845169588724831345244050625878216011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-73036147505505905955956388950825000000000000)
      constant := (735835969782449204259970055265491908091225101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree039.table
  base := (-63721265499775247764242351555080769779/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-92067876876071998369303174729505604687500000000)
      constant := (927833197992329174762667096244396113112059808725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61544337460747936729/20000000000000000000)
  centralHi := (153860843651869841823/50000000000000000000)
  directionLo := (311744363754619731237/100000000000000000000)
  directionHi := (155872181877309865619/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree040.table
  base := (-1636735990078853402189160205625620923183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-18726393238312113063745011790006250000000000)
      constant := (193605765576534677337815313761397630826778953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree040.table
  base := (-6547186585009237382228353416676059025981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1133093250322846255923560306176176825000000000000)
      constant := (11717862059660327255925895624475502382814400947633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311744363754619731237/100000000000000000000)
  centralHi := (155872181877309865619/50000000000000000000)
  directionLo := (157857894820376962999/50000000000000000000)
  directionHi := (315715789640753925999/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree041.table
  base := (-6697136553931296257959003018220216136367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-76774998400990998554003705369225000000000000)
      constant := (814067737328772681995798471249319412872945097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree041.table
  base := (-6697345642163482891536392440260996317131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1161371978132828531415482515598286393750000000000)
      constant := (12317727168868277775955607865300919077209079834583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157857894820376962999/50000000000000000000)
  centralHi := (315715789640753925999/100000000000000000000)
  directionLo := (499434180151113703/156250000000000000)
  directionHi := (319637875296712769921/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree042.table
  base := (-1364602269565507072750087561833846776653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-78644423848733544853027363578425000000000000)
      constant := (854768342042079346492883820832243622021908615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree042.table
  base := (-6823191437645218810594231399200890664879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-396550235314270268969134908340131987500000000000)
      constant := (4311189579016480982154120421160618814641040995449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499434180151113703/156250000000000000)
  centralHi := (319637875296712769921/100000000000000000000)
  directionLo := (323512415248486287847/100000000000000000000)
  directionHi := (40439051906060785981/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree043.table
  base := (-6925062726943563077637313379074568467959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-80513849296476091152051021787625000000000000)
      constant := (896523487718763837928935915566279537173503169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree043.table
  base := (-692521776004399293465520049944257825359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-608964716876396541199663467221252765625000000000)
      constant := (6782682893907093981101531079215639233399379864935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323512415248486287847/100000000000000000000)
  centralHi := (40439051906060785981/12500000000000000000)
  directionLo := (5114704653285191703/1562500000000000000)
  directionHi := (327341097810252268993/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree044.table
  base := (-7003706123825581382814388685539389251031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-82383274744218637451074679996825000000000000)
      constant := (939332007408803874933160677539519855593853921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree044.table
  base := (-7003839520618464115173029524967093719577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1246208161562775357891249143864615100000000000000)
      constant := (14213100695521884987027918421884670316100853214461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5114704653285191703/1562500000000000000)
  centralHi := (327341097810252268993/100000000000000000000)
  directionLo := (165562756841124494497/50000000000000000000)
  directionHi := (66225102736449797799/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree045.table
  base := (-7059290658000061584358381704360223595447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-84252700191961183750098338206025000000000000)
      constant := (983192920435449599609597605957952131920389377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree045.table
  base := (-1764851345964879014452015422061345316151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-106207240781063136115264279440560389062500000000)
      constant := (1239729887394015698686869992031854796614146535481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165562756841124494497/50000000000000000000)
  centralHi := (66225102736449797799/20000000000000000000)
  directionLo := (83716790918490995249/25000000000000000000)
  directionHi := (334867163673963980997/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree046.table
  base := (-7092109745463728504214745378260852229631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-86122125639703730049121996415225000000000000)
      constant := (1028105402593166211933401923505465266086966521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree046.table
  base := (-177305209226868110322421071143544090837/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-162845702147842488609386695338604279687500000000)
      constant := (1944540899978043943909934427164085817374294678205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83716790918490995249/25000000000000000000)
  centralHi := (334867163673963980997/100000000000000000000)
  directionLo := (338567465658999050869/100000000000000000000)
  directionHi := (33856746565899905087/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree047.table
  base := (-710241000564235634767550422996749340591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-43995775543723138174072827312212500000000000)
      constant := (537034380563993356080954166648860655511399405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree047.table
  base := (-177562368757046048360389936804329113263/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-166380543124090273045876971516367975781250000000)
      constant := (2031474485870654928018683584880521706816878865795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338567465658999050869/100000000000000000000)
  centralHi := (33856746565899905087/10000000000000000000)
  directionLo := (85556940213254186513/25000000000000000000)
  directionHi := (342227760853016746053/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree048.table
  base := (-3545199370048648437756285298103523111171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-44930488267594411323584656416812500000000000)
      constant := (560541206864912631599554266790427203580720661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree048.table
  base := (-7090471528623072084848745071175544802839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-453107690934234819952979327184351125000000000000)
      constant := (5654385305545793873556308689820524981924728080209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85556940213254186513/25000000000000000000)
  centralHi := (342227760853016746053/100000000000000000000)
  directionLo := (34584931949359354033/10000000000000000000)
  directionHi := (345849319493593540331/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree049.table
  base := (-3528125106424397438641821992646406046007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-45865200991465684473096485521412500000000000)
      constant := (584572935445524498715567473218006245416766337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree049.table
  base := (-441019544193876864726725535457263306247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-173450225076585841918857523871895367968750000000)
      constant := (2211299987138120631752331809381068549268879533042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34584931949359354033/10000000000000000000)
  centralHi := (345849319493593540331/100000000000000000000)
  directionLo := (13977333839607258113/4000000000000000000)
  directionHi := (174716672995090726413/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree050.table
  base := (-3500055462506200041930034436483974008909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-46799913715336957622608314626012500000000000)
      constant := (609129360545012167831984982615416517008974619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree050.table
  base := (-3500082280137138421552653727274809171903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-707940264211334505421391200198636256250000000000)
      constant := (9216760807275354132683506804335162774533685405179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13977333839607258113/4000000000000000000)
  centralHi := (174716672995090726413/50000000000000000000)
  directionLo := (176490491801687421679/50000000000000000000)
  directionHi := (352980983603374843359/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree051.table
  base := (-1384420809064026486072812766739743519273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-95469252878416461544240287461225000000000000)
      constant := (1268420618345783033899855277989640302271810715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree051.table
  base := (-6922150060400575673343916306741105529819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-481386418744217095444901536606460693750000000000)
      constant := (6397505281683542374900355182985765876958740920589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176490491801687421679/50000000000000000000)
  centralHi := (352980983603374843359/100000000000000000000)
  directionLo := (44561664838127348701/12500000000000000000)
  directionHi := (356493318705018789609/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree052.table
  base := (-3411166566014912310007563439211917601161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-48669339163079503921631972835212500000000000)
      constant := (659815635881589420037723657399853723458338751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree052.table
  base := (-3411186297753716846000769908343193571647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-736218992021316780913313409620745825000000000000)
      constant := (9983689098314468934844209809950211758639794614971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44561664838127348701/12500000000000000000)
  centralHi := (356493318705018789609/100000000000000000000)
  directionLo := (359971384664156630261/100000000000000000000)
  directionHi := (179985692332078315131/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree053.table
  base := (-3350442629943378707115781107525354882933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (88)
      previous := (44)
      next := (44)
      square := (314930163029404699970292825000000000000)
      linear := (-17658971835867133168794518312500000000000)
      constant := (244195520959283065242421156842474645117067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree053.table
  base := (-6700919092964288655840380234434076279077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (2661648)
      previous := (1330824)
      next := (1330824)
      square := (9525377710987374555301476784950000000000000)
      linear := (-534253012407481608158970818320968750000000000)
      constant := (7389855812234572662198958629932750925369018529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359971384664156630261/100000000000000000000)
  centralHi := (179985692332078315131/50000000000000000000)
  directionLo := (11356755168694200579/3125000000000000000)
  directionHi := (363416165398214418529/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree054.table
  base := (-6557833647500495600600507050100105227571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-101077529221644100441311262088825000000000000)
      constant := (1425197907632929027780947242600468804415753061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree054.table
  base := (-819732830486220920633685748101382267881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-63708143319274921367102968253571282812500000000)
      constant := (898528878329865869848740124192713402347733018111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11356755168694200579/3125000000000000000)
  centralHi := (363416165398214418529/100000000000000000000)
  directionLo := (366828598624009219189/100000000000000000000)
  directionHi := (36682859862400921919/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree055.table
  base := (-1278647973031948666979960421948398939699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-102946954669386646740334920298025000000000000)
      constant := (1479553511463268171848942910578234736891927545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree055.table
  base := (-6393264708363673803120653002633652787589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1557274167472580388302393447507820356250000000000)
      constant := (22387139895823186340770281896100960210532193472377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366828598624009219189/100000000000000000000)
  centralHi := (36682859862400921919/10000000000000000000)
  directionLo := (370209578839022718793/100000000000000000000)
  directionHi := (185104789419511359397/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree056.table
  base := (-38794723064043503423626455055606609253/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-13102047514641149129919822313403125000000000)
      constant := (191869637849700295348838875855476020692166460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree056.table
  base := (-3103588484282254268559372327426702963831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-792776447641281331897157828464964962500000000000)
      constant := (11612721614400492716363589904887392152758056457683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370209578839022718793/100000000000000000000)
  centralHi := (185104789419511359397/50000000000000000000)
  directionLo := (186779980029899549201/50000000000000000000)
  directionHi := (373559960059799098403/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree057.table
  base := (-239984986665177020264517635335149707431/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-106685805564871739338382236716425000000000000)
      constant := (1591408559321208415953205994261289111795658025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree057.table
  base := (-5999642886171313448160670829879049776713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-537943874364181646428745955450679831250000000000)
      constant := (8026533744192005793952408757817892524547644155503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186779980029899549201/50000000000000000000)
  centralHi := (373559960059799098403/100000000000000000000)
  directionLo := (376880558341221439581/100000000000000000000)
  directionHi := (188440279170610719791/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree058.table
  base := (-5770683415357403922696848077466601604089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-108555231012614285637405894925625000000000000)
      constant := (1648907778165556134953389201650996316094113999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree058.table
  base := (-90167172051975529203047850422578604427/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-205263793862815901847270009471768632812500000000)
      constant := (3118701544309963054532021967872255846432552514088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376880558341221439581/100000000000000000000)
  centralHi := (188440279170610719791/50000000000000000000)
  directionLo := (190086077048861561813/50000000000000000000)
  directionHi := (380172154097723123627/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree059.table
  base := (-5520362736411195217962475966404808110109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-110424656460356831936429553134825000000000000)
      constant := (1707454672813500858715057793908068894018703819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree059.table
  base := (-345023505179404109378987490889992868497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-208798634839063686283760285649532328906250000000)
      constant := (3229434411088814185970888783073427504645780911542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190086077048861561813/50000000000000000000)
  centralHi := (380172154097723123627/100000000000000000000)
  directionLo := (191717747122570173667/50000000000000000000)
  directionHi := (76687098849028069467/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree060.table
  base := (-5248688534871179249813068354144469752529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-112294081908099378235453211344025000000000000)
      constant := (1767049170497671800218766059187208184465146039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree060.table
  base := (-1049739990639260159435977603973807595079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-566222602174163921920668164872789400000000000000)
      constant := (8912396312348562444510332847526415486275988958245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191717747122570173667/50000000000000000000)
  centralHi := (76687098849028069467/20000000000000000000)
  directionLo := (38667129417985914929/10000000000000000000)
  directionHi := (386671294179859149291/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree061.table
  base := (-198227303981644893903760752906894198301/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-114163507355841924534476869553225000000000000)
      constant := (1827691210013319179845382786916613354924312275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree061.table
  base := (-991138473145666860824900225149956925877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1726946534332474041253926704040477768750000000000)
      constant := (27654752375813533745299602349805006908451355601805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38667129417985914929/10000000000000000000)
  centralHi := (386671294179859149291/100000000000000000000)
  directionLo := (194940119805056608837/50000000000000000000)
  directionHi := (15595209584404528707/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree062.table
  base := (-2320681628784790441713766025420565356379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-58016466401792235416750263881212500000000000)
      constant := (944690369939741351372808352076693631913931389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree062.table
  base := (-4641371608550224068103035051466914667067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1755225262142456316745848913462587337500000000000)
      constant := (28588164828126986881433133286164228607936007637031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194940119805056608837/50000000000000000000)
  centralHi := (15595209584404528707/4000000000000000000)
  directionLo := (98265747063177937513/25000000000000000000)
  directionHi := (393062988252711750053/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree063.table
  base := (-861149184969756020073021728322663029373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-117902358251327017132524185971625000000000000)
      constant := (1952117716792921108211736145703808197752456215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree063.table
  base := (-1076438265985402694780563760207504033003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-148625332496036549353147593573724742187500000000)
      constant := (2461452136711584065803522844222491803810824067493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98265747063177937513/25000000000000000000)
  centralHi := (393062988252711750053/100000000000000000000)
  directionLo := (198110085703544845307/50000000000000000000)
  directionHi := (79244034281417938123/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree064.table
  base := (-3948843568808823408623748750162738826173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-119771783699069563431547844180825000000000000)
      constant := (2015902104328123235764441558131992866637280043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree064.table
  base := (-3948849670424922322425371051815248407287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1811782717762420867729693332306806475000000000000)
      constant := (30502534263414606902490955505999750077327505745491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198110085703544845307/50000000000000000000)
  centralHi := (79244034281417938123/20000000000000000000)
  directionLo := (1996761977086751159/500000000000000000)
  directionHi := (399352395417350231801/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree065.table
  base := (-3570667097570273842242406716446281890189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-121641209146812109730571502390025000000000000)
      constant := (2080733871844178423841117518697002394170459099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree065.table
  base := (-892668077817643409042191279369562671761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-460015361393100785805403885432229010937500000000)
      constant := (7870872558606734043826480164525969897638052512173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/500000000000000000)
  centralHi := (399352395417350231801/100000000000000000000)
  directionLo := (25153765189493110303/6250000000000000000)
  directionHi := (402460243031889764849/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree066.table
  base := (-1585612843594272466412198207577234442031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-61755317297277328014797580299612500000000000)
      constant := (1073306496782773507915745159362415548452334921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree066.table
  base := (-3171230141181057489103156396629248335039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-622780057794128472904512583717008537500000000000)
      constant := (10826764388226531093702268426833806098389129138409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25153765189493110303/6250000000000000000)
  centralHi := (402460243031889764849/100000000000000000000)
  directionLo := (405544274669239898051/100000000000000000000)
  directionHi := (101386068667309974513/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree067.table
  base := (-137526352842540585485735524697850270209/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-31345015010574300582154704702106250000000000)
      constant := (553384861952258059269532468467043692954914595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree067.table
  base := (-2750530861003286247516970346947134884561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-1896618901192367694205459960573135181250000000000)
      constant := (33492942727036697053189107351518459750679899747573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405544274669239898051/100000000000000000000)
  centralHi := (101386068667309974513/25000000000000000000)
  directionLo := (408605029597913800841/100000000000000000000)
  directionHi := (204302514798956900421/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree068.table
  base := (-1154288850156500540874080501898684443747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-63624742745019874313821238508812500000000000)
      constant := (1140756608166836844447059598537966595397514677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree068.table
  base := (-1154290474373402532268875542244885406293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-962448814501174984848691084997622375000000000000)
      constant := (17260719323154558831304288080719999601346272369449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408605029597913800841/100000000000000000000)
  centralHi := (204302514798956900421/50000000000000000000)
  directionLo := (51455378379661411983/12500000000000000000)
  directionHi := (82328605407458259173/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree069.table
  base := (-184538308054278024359128675645849670569/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-64559455468891147463333067613412500000000000)
      constant := (1175267141896997597064819990412904041376858395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree069.table
  base := (-1845385853865105592875854951341143560239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-651058785604110748396434793139118106250000000000)
      constant := (11855260230333769303679269282901214476041566579609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51455378379661411983/12500000000000000000)
  centralHi := (82328605407458259173/20000000000000000000)
  directionLo := (5183234589823837931/1250000000000000000)
  directionHi := (414658767185907034481/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree070.table
  base := (-680473896712004479864286777737085861101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-65494168192762420612844896718012500000000000)
      constant := (1210301318640079495353127652247836525816167291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree070.table
  base := (-680475080323959665880737251985907530313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-990727542311157260340613294419731943750000000000)
      constant := (18312984333185157884747816861901448412741560891309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5183234589823837931/1250000000000000000)
  centralHi := (414658767185907034481/100000000000000000000)
  directionLo := (41765273218290859401/10000000000000000000)
  directionHi := (417652732182908594011/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree071.table
  base := (-213818926361255453017653276553109457429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-33214440458316846881178362911306250000000000)
      constant := (622929566482799836695844578996287315534081939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree071.table
  base := (-427638862820120663801023003605011255057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42135000000000000000000000000000000000000000
      center := (741576)
      previous := (370788)
      next := (370788)
      square := (2653916483848793406649657636275000000000000)
      linear := (-199338803058152826440502757216978125000000000)
      constant := (3739536045287458299950225884312405238122384661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41765273218290859401/10000000000000000000)
  centralHi := (417652732182908594011/100000000000000000000)
  directionLo := (420625387007917642193/100000000000000000000)
  directionHi := (210312693503958821097/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree072.table
  base := (-328370069508964269563835643733831820817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-134727187281009933823737109854425000000000000)
      constant := (2563881160609711326738738492763951666415325047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree072.table
  base := (-328371793220546639439742131522429252203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-679337513414093023888357002561227675000000000000)
      constant := (12931293926610660607483490781594997999498261897693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420625387007917642193/100000000000000000000)
  centralHi := (210312693503958821097/50000000000000000000)
  directionLo := (42357718032404981203/10000000000000000000)
  directionHi := (423577180324049812031/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree073.table
  base := (6867699301706647852375839917671675419/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-17074576591094060015345096007953125000000000)
      constant := (329636414203527702748957892971452458945007884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree073.table
  base := (219764907187607883850240912242775369953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2066291268052261347156993217105792593750000000000)
      constant := (39901606664154500983868977946483560005388653506171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42357718032404981203/10000000000000000000)
  centralHi := (423577180324049812031/100000000000000000000)
  directionLo := (213254272634210503187/50000000000000000000)
  directionHi := (3412068362147368051/800000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree074.table
  base := (78913133355160027536194932061077354857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-69233019088247513210892213136412500000000000)
      constant := (1355674359259512140299836407699897831448966565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree074.table
  base := (19728251983741320565521022516168927261/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-261821249482780452831114428315987770312500000000)
      constant := (5128147120501312920560048900802642333540810756635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213254272634210503187/50000000000000000000)
  centralHi := (3412068362147368051/800000000000000000)
  directionLo := (17176796007763350063/4000000000000000000)
  directionHi := (53677487524260468947/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree075.table
  base := (1379722860998913187228318029242298899059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-140335463624237572720808084482025000000000000)
      constant := (2786653369840572016304884598886641617607456731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree075.table
  base := (689860895721910065390344542758213206359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-353808120612037649690139605991668621875000000000)
      constant := (7027432099555870137341725235308563636956481564671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17176796007763350063/4000000000000000000)
  centralHi := (53677487524260468947/12500000000000000000)
  directionLo := (432311649366991925413/100000000000000000000)
  directionHi := (216155824683495962707/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree076.table
  base := (497884832536370960140200022923248921269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-35551222267995029754957935672806250000000000)
      constant := (715751315753653295036245383270891406219844621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree076.table
  base := (1991538418209659738538825641573994237079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2151127451482208173632759845372121300000000000000)
      constant := (43319853495086765436565953205379857568831194119053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432311649366991925413/100000000000000000000)
  centralHi := (216155824683495962707/50000000000000000000)
  directionLo := (43518418362128131187/10000000000000000000)
  directionHi := (435184183621281311871/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree077.table
  base := (262457936969937416415212109118391527979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-72037157259861332659427700450212500000000000)
      constant := (1470202197094594359038971192076917809010465055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree077.table
  base := (1312289296142403765694047835969799507011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1089703089646095224562341027397115434375000000000)
      constant := (22245479799589445360862163295929788336445396084577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43518418362128131187/10000000000000000000)
  centralHi := (435184183621281311871/100000000000000000000)
  directionLo := (438037880975873146259/100000000000000000000)
  directionHi := (21901894048793657313/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree078.table
  base := (3278841825898334800254084839417533675363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-145943739967465211617879059109625000000000000)
      constant := (3018850760123380471657852469004523852094094667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree078.table
  base := (3278841163269795144197751856724448780207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-735894969034057574872201421405446812500000000000)
      constant := (15225970286914014670281418767950924022565824974983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438037880975873146259/100000000000000000000)
  centralHi := (21901894048793657313/5000000000000000000)
  directionLo := (110218276803788685669/25000000000000000000)
  directionHi := (440873107215154742677/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree079.table
  base := (988581431998429502035616692284075723777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-36953291353801939479225679329706250000000000)
      constant := (774586089522588872345254360206550968708089593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree079.table
  base := (3954325163292937969989162946961860752641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2235963634912155000108526473638450006250000000000)
      constant := (46880707238660545430877194347737295842521528768987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218276803788685669/25000000000000000000)
  centralHi := (440873107215154742677/100000000000000000000)
  directionLo := (443690216436262484809/100000000000000000000)
  directionHi := (44369021643626248481/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree080.table
  base := (930206051842641399548725019920594479837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-149682590862950304215926375528025000000000000)
      constant := (3178885185795800333384120439856784749469310665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree080.table
  base := (4651029778042605543069095327594812991607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2264242362722137275600448683060559575000000000000)
      constant := (48099348698342024063643846053076082871453652104749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443690216436262484809/100000000000000000000)
  centralHi := (44369021643626248481/10000000000000000000)
  directionLo := (223244775782642653997/50000000000000000000)
  directionHi := (89297910313057061599/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree081.table
  base := (5368954732332260339899184857290860891663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-151552016310692850514950033737225000000000000)
      constant := (3260473241309301266792655590795630028244681367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree081.table
  base := (2684477161199182008022532039298041502993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-382086848422019925182061815413778190625000000000)
      constant := (8222305868447036087207836338746087048211551135817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223244775782642653997/50000000000000000000)
  centralHi := (89297910313057061599/20000000000000000000)
  directionLo := (17970857793780760431/4000000000000000000)
  directionHi := (56158930605564876347/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree082.table
  base := (3054049284561222437194383525941367100881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-76710720879217698406986845973212500000000000)
      constant := (1671554261503307310429781924529469300186374729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree082.table
  base := (38175613874565862294435564062622845259/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-290099977292762728323036637738097339062500000000)
      constant := (6323020843899262243490361746475472466573791076260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17970857793780760431/4000000000000000000)
  centralHi := (56158930605564876347/12500000000000000000)
  directionLo := (226018109146365640961/50000000000000000000)
  directionHi := (452036218292731281923/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree083.table
  base := (6868461283061111480282484749658828524271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-155290867206177943112997350155625000000000000)
      constant := (3426791029521098274204153162249891649324677239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree083.table
  base := (1717115246413457845784463600915403787141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-587269636538021025519053827831722070312500000000)
      constant := (12962585824818811768872210035721849435493329135487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226018109146365640961/50000000000000000000)
  centralHi := (452036218292731281923/100000000000000000000)
  directionLo := (90956836828048484379/20000000000000000000)
  directionHi := (56848023017530302737/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree084.table
  base := (3825021232392328802906357810217527984163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-78580146326960244706010504182412500000000000)
      constant := (1755760379851424933629254139621501036107513867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree084.table
  base := (7650042211518274071102146712255810508981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-792452424654022125856045840249665950000000000000)
      constant := (17710788279197164763603388103789442582414146977789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90956836828048484379/20000000000000000000)
  centralHi := (56848023017530302737/12500000000000000000)
  directionLo := (2287578226202428943/500000000000000000)
  directionHi := (457515645240485788601/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree085.table
  base := (1056605221231232798427412301086035447061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-19878714762707879463880583321753125000000000)
      constant := (449662214073041049077111088383938173570794349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree085.table
  base := (8452841554202860502596549736076587785029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2405636001772048653060059730171107418750000000000)
      constant := (54430231351558389215290375954556182045211476429703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2287578226202428943/500000000000000000)
  centralHi := (457515645240485788601/100000000000000000000)
  directionLo := (115057723864895899377/25000000000000000000)
  directionHi := (460230895459583597509/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree086.table
  base := (4638429454218474498451558952399153131157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-80449571774702791005034162391612500000000000)
      constant := (1842060943675715048584441565555789221145420013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree086.table
  base := (1159607340605786851167645120512249912513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-304239341197753866068997742449152123437500000000)
      constant := (6967992853613119693470992449484000661052851634091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115057723864895899377/25000000000000000000)
  centralHi := (460230895459583597509/100000000000000000000)
  directionLo := (462930220045356604313/100000000000000000000)
  directionHi := (231465110022678302157/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree087.table
  base := (2530523409171551163690986613988941937433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-40692142249287032077272995748106250000000000)
      constant := (942998320829788261929218852971619937902249297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree087.table
  base := (2530523370101831482303202684051838058373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-205182788116001100336992012417943879687500000000)
      constant := (4756124938275556976767464540975599384059771670037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462930220045356604313/100000000000000000000)
  centralHi := (231465110022678302157/50000000000000000000)
  directionLo := (116403473994269820189/25000000000000000000)
  directionHi := (465613895977079280757/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree088.table
  base := (10988545749408920250116265662655954951969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-164637994444890674608115641201625000000000000)
      constant := (3860911899911122160368388128212000577460080921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree088.table
  base := (1098854561639599727580153268396403335061/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1245236092600997739767913179218718062500000000000)
      constant := (29209450317038365351708297980438718978249410779635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116403473994269820189/25000000000000000000)
  centralHi := (465613895977079280757/100000000000000000000)
  directionLo := (468282192297194368583/100000000000000000000)
  directionHi := (58535274037149296073/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree089.table
  base := (11876215073954568914160250271058414929519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-166507419892633220907139299410825000000000000)
      constant := (3950877736642362105148962570950103087537018871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree089.table
  base := (2969053740189553514701829726906166845219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-629687728252994438756937141964886423437500000000)
      constant := (14945036736476538329067750246424409395095478021033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468282192297194368583/100000000000000000000)
  centralHi := (58535274037149296073/12500000000000000000)
  directionLo := (94187074085222255497/20000000000000000000)
  directionHi := (235467685213055638743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree090.table
  base := (3196275366262690580588154820772133743061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-42094211335093941801540739405006250000000000)
      constant := (1010472698276200685813739165944298923684258349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree090.table
  base := (1278510136873058296798905567956191964479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-424504940136993338419945129546942543750000000000)
      constant := (10192873031440888202818889793795587066020448184755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94187074085222255497/20000000000000000000)
  centralHi := (235467685213055638743/50000000000000000000)
  directionLo := (473573684461130888997/100000000000000000000)
  directionHi := (236786842230565444499/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree091.table
  base := (3428801200115411077515432227840942513211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-42561567697029578376296653957306250000000000)
      constant := (1033487767238770888679980029823630207519609699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree091.table
  base := (13715204718511541257918301132719333017481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2575308368631942306011592986703764831250000000000)
      constant := (62550174357120066266525497149372507507432870242867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473573684461130888997/100000000000000000000)
  centralHi := (236786842230565444499/50000000000000000000)
  directionLo := (476197381460464231761/100000000000000000000)
  directionHi := (238098690730232115881/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree092.table
  base := (7333262488667438771356361798765766042279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-86057848117930429902105137019212500000000000)
      constant := (2113529281952146161985516084119333036812761711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree092.table
  base := (14666524907619238036626048417545213856549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2603587096441924581503515196125874400000000000000)
      constant := (63958955446976883480918230506239164245674626790343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476197381460464231761/100000000000000000000)
  centralHi := (238098690730232115881/50000000000000000000)
  directionLo := (14962709428538861569/3125000000000000000)
  directionHi := (478806701713243570209/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree093.table
  base := (312781238182559708176391070795404071773/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-86992560841801703051616966123812500000000000)
      constant := (2160606638854665617103314248358157250940258925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree093.table
  base := (3909765462456798398857070542846374510299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-219322152020992238082953117128998664062500000000)
      constant := (5448631787879403023770119129831013258448829205531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14962709428538861569/3125000000000000000)
  centralHi := (478806701713243570209/100000000000000000000)
  directionLo := (481401878996361129523/100000000000000000000)
  directionHi := (120350469749090282381/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree094.table
  base := (8316407761511073017270433941132695610311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-87927273565672976201128795228412500000000000)
      constant := (2208207605082826107391544375086741741969363599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree094.table
  base := (1663281547258605999862969441236721856827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1330072276030944566243679807485046768750000000000)
      constant := (33412026188382995798333677111990190813339336856445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481401878996361129523/100000000000000000000)
  centralHi := (120350469749090282381/25000000000000000000)
  directionLo := (3781118287647753547/781250000000000000)
  directionHi := (483983140818912454017/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree095.table
  base := (17647785757746118104226804812529473825689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-177723972579088498701281248666025000000000000)
      constant := (4512664361101144348844752466778895291976360401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree095.table
  base := (17647785714854356806723836992935707331981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2688423279871871407979281824392203106250000000000)
      constant := (68280368211023276378095187757186498710202107694367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3781118287647753547/781250000000000000)
  centralHi := (483983140818912454017/100000000000000000000)
  directionLo := (243275354327483902049/50000000000000000000)
  directionHi := (486550708654967804099/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree096.table
  base := (18683972561745246131975721336941283127563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-179593398026831045000304906875225000000000000)
      constant := (4609960730370990609131721931363468064305324467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree096.table
  base := (583874141414790504313894279451290581213/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-113195916986743903477966834742263028125000000000)
      constant := (2906355373130955970058595771812007351342337219988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243275354327483902049/50000000000000000000)
  centralHi := (486550708654967804099/100000000000000000000)
  directionLo := (97820959633069125117/20000000000000000000)
  directionHi := (244552399082672812793/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree097.table
  base := (1233835993227550850070030320704602186161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-22682852934321698912416070635553125000000000)
      constant := (588538039731667522618584896153555955081852498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree097.table
  base := (1974137586063110829801885474923869178867/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1372490367745917979481563121618211121875000000000)
      constant := (35620267303644667210803991354314355009955187977845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97820959633069125117/20000000000000000000)
  centralHi := (244552399082672812793/50000000000000000000)
  directionLo := (245822809704508300553/50000000000000000000)
  directionHi := (491645619409016601107/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree098.table
  base := (5204998927733423795300937806323672053411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-45833062230579034399588055823406250000000000)
      constant := (1201923780861416755310592374588113194798031499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree098.table
  base := (2602499460571367699374691453270609006393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-346657432912727279306881056582316476562500000000)
      constant := (9093048145739749038239397791059611188848934631251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245822809704508300553/50000000000000000000)
  centralHi := (491645619409016601107/100000000000000000000)
  directionLo := (247086688522362390351/50000000000000000000)
  directionHi := (494173377044724780703/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree099.table
  base := (21919831988913564121573617677795495033201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-185201674370058683897375881502825000000000000)
      constant := (4908133147061705822170211726182627545548261609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree099.table
  base := (273997899581296216616613884644008353259/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-116730757962991687914457110920026724218750000000)
      constant := (3094336692905394854703902474015307318915317970210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247086688522362390351/50000000000000000000)
  centralHi := (494173377044724780703/100000000000000000000)
  directionLo := (496688270523373483491/100000000000000000000)
  directionHi := (124172067630843370873/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree100.table
  base := (23040884699741056664093500689465280942171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-187071099817801230196399539712025000000000000)
      constant := (5009618388628873810935600188826707974166558339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree100.table
  base := (11520442340346645821930927574192353115647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1414908459460891392719446435751375475000000000000)
      constant := (37899810498815252576048546243520535377438214193029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496688270523373483491/100000000000000000000)
  centralHi := (124172067630843370873/25000000000000000000)
  directionLo := (499190494271687789751/100000000000000000000)
  directionHi := (62398811783960973719/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree101.table
  base := (24183153821675465921930919678739312036757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-188940525265543776495423197921225000000000000)
      constant := (5112150848086101341893422448331078727511250413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree101.table
  base := (6045788451371748405150343386650442480789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-714523911682941265232703770231215129687500000000)
      constant := (19337751567175314809048626124683559421864113855023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499190494271687789751/100000000000000000000)
  centralHi := (62398811783960973719/12500000000000000000)
  directionLo := (62710029733454031781/12500000000000000000)
  directionHi := (501680237867632254249/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree102.table
  base := (25346639336424887918838281398516568038909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-190809950713286322794446856130425000000000000)
      constant := (5215730525382006456774399015264633039621295381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree102.table
  base := (2534663932266782818298479137773003027947/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-481062395756957889403789548391161681250000000000)
      constant := (13153039407027978737987856780258741868894331215215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62710029733454031781/12500000000000000000)
  centralHi := (501680237867632254249/100000000000000000000)
  directionLo := (126039421552007935467/25000000000000000000)
  directionHi := (504157686208031741869/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree103.table
  base := (13265670614299701287624409776357789202903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-96339688080514434546735257169812500000000000)
      constant := (2660178710236679435037513421550839029870954527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree103.table
  base := (6632835304227420740014619781028717655659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-728663275587932402978664874942269914062500000000)
      constant := (20125327879344820925859479695023894441312480114113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126039421552007935467/25000000000000000000)
  centralHi := (504157686208031741869/100000000000000000000)
  directionLo := (101324603933762962197/20000000000000000000)
  directionHi := (253311509834407405493/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree104.table
  base := (27737259485250951891077244108052634256317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-194548801608771415392494172548825000000000000)
      constant := (5426031533323787486873066352138719849625994453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree104.table
  base := (27737259475318829592937552017032353782869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-2942931830161711887406581709191189225000000000000)
      constant := (82100231493787760944921130934751646749099643034583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101324603933762962197/20000000000000000000)
  centralHi := (253311509834407405493/50000000000000000000)
  directionLo := (15908637945571020723/3125000000000000000)
  directionHi := (509076414258272663137/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree105.table
  base := (56571082217746422945458315242460363981/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-24552278382064245211439728844753125000000000)
      constant := (691594107987836604796444548605966054395048256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree105.table
  base := (5792878817409630792352510066237943039677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-990403519323898054299501306204432931250000000000)
      constant := (27904998790310837748359429509214713600966312627065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15908637945571020723/3125000000000000000)
  centralHi := (509076414258272663137/100000000000000000000)
  directionLo := (818428866821923473/160000000000000000)
  directionHi := (255759020881851085313/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree106.table
  base := (3776593131267573518464418839864270824989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78732540757351174992573206250000000000)
      linear := (-8823765241378449091782729128125000000000)
      constant := (251002198833407437881587675214864270824989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree106.table
  base := (604254900859451276581088800365939670717/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75615000000000000000000000000000000000000000
      center := (1330824)
      previous := (665412)
      next := (665412)
      square := (4762688855493687277650738392475000000000000)
      linear := (-533906957241309440795732667859631250000000000)
      constant := (15191457128591296201359828727399686625381329775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (818428866821923473/160000000000000000)
  centralHi := (255759020881851085313/50000000000000000000)
  directionLo := (32121754368236170827/6250000000000000000)
  directionHi := (513948069891778733233/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree107.table
  base := (7870578085376128130251854590764048354951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-50039269487999763572391286794106250000000000)
      constant := (1437334294536762065456703408699881211829057359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree107.table
  base := (15741156167707935749154942976726471801027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1513884006795829356941174168728758965625000000000)
      constant := (43496030412970919521115097460058415389128048830689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32121754368236170827/6250000000000000000)
  centralHi := (513948069891778733233/100000000000000000000)
  directionLo := (32272916400186472599/6250000000000000000)
  directionHi := (103273332480596712317/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree108.table
  base := (327730959630923348517946080479465984189/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-50506625849935400147147201346406250000000000)
      constant := (1464800040443155930520074917070570498739672525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree108.table
  base := (8193273989480247002613660146431020982481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2229732165846961260486820690743712500000000000)
      linear := (-254670561783470082447855878906635625000000000000)
      constant := (7387863366933835315110395302482762571923226999289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32272916400186472599/6250000000000000000)
  centralHi := (103273332480596712317/20000000000000000000)
  directionLo := (103754795848078062099/20000000000000000000)
  directionHi := (16211686851262197203/3125000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree109.table
  base := (8521273977362108974090056852969892553087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-50973982211871036721903115898706250000000000)
      constant := (1492527590761433372594974037258167428181621383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree109.table
  base := (6817019181011312038377821253347548447023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3084325469211623264866192756301737068750000000000)
      constant := (90332504879987729640012593996461521297081435903305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103754795848078062099/20000000000000000000)
  centralHi := (16211686851262197203/3125000000000000000)
  directionLo := (521170176653097674577/100000000000000000000)
  directionHi := (260585088326548837289/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree110.table
  base := (7083662435196770637385447859416192416563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-205765354295226693186636121804025000000000000)
      constant := (6082067781953487171153617379674500422490627335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree110.table
  base := (35418312172254271263722908430674406107987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3112604197021605540358114965723846637500000000000)
      constant := (92026494256092892205389876011146024322609934509409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521170176653097674577/100000000000000000000)
  centralHi := (260585088326548837289/50000000000000000000)
  directionLo := (130888851828644376157/25000000000000000000)
  directionHi := (523555407314577504629/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree111.table
  base := (18386372379419422220665010997019469289571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-103817389871484619742829890006612500000000000)
      constant := (3097536209242521374165430064412877689234404939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree111.table
  base := (183863723778359711556966738728034310849/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-130870121867982825660418215631081508593750000000)
      constant := (3905680355473262240382552355122409609509923399525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130888851828644376157/25000000000000000000)
  centralHi := (523555407314577504629/100000000000000000000)
  directionLo := (131482455109048027417/25000000000000000000)
  directionHi := (525929820436192109669/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree112.table
  base := (38148393654767239948982892796091444154069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-209504205190711785784683438222425000000000000)
      constant := (6309124272631281731194589213763420866628779821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree112.table
  base := (4768549206509792889253761018608312314889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-396145206580196261417744923071008221875000000000)
      constant := (11932750963205833754171305209329299225925828368723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131482455109048027417/25000000000000000000)
  centralHi := (525929820436192109669/100000000000000000000)
  directionLo := (105658712375223917497/20000000000000000000)
  directionHi := (264146780938059793743/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree113.table
  base := (19772629430519564793580944356635987863903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-105686815319227166041853548215812500000000000)
      constant := (3212111672192267901105036511224340489909703527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree113.table
  base := (39545258858756269709513343250260757408477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3197440380451552366833881593990175343750000000000)
      constant := (97203531778842592796024174145648634179377046557839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105658712375223917497/20000000000000000000)
  centralHi := (264146780938059793743/50000000000000000000)
  directionLo := (132661693560978048737/25000000000000000000)
  directionHi := (530646774243912194949/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree114.table
  base := (40963340375358977796070661724668167657719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-213243056086196878382730754640825000000000000)
      constant := (6540369633738356801989843613290792882950532671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree114.table
  base := (40963340373420992029766641209290777866779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1075239702753844880775267934470761637500000000000)
      constant := (32986966916949668521830806965808312332391300125651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132661693560978048737/25000000000000000000)
  centralHi := (530646774243912194949/100000000000000000000)
  directionLo := (33311849812556240863/6250000000000000000)
  directionHi := (532989597000899853809/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree115.table
  base := (662541221809323760539157754861136778957/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-26889060191742428085219301606253125000000000)
      constant := (832195392585915397629427679349551965696721704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree115.table
  base := (66254122178361928605917669487197741121/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-406749729508939614727215751604299310156250000000)
      constant := (12591764327698038570663611810878439758731415955260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33311849812556240863/6250000000000000000)
  centralHi := (532989597000899853809/100000000000000000000)
  directionLo := (107064433311327764023/20000000000000000000)
  directionHi := (133830541639159705029/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree116.table
  base := (548289404009122339025493961759597309153/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-27122738372710246372597258882403125000000000)
      constant := (846975483153359642140712792174577088414107770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree116.table
  base := (685361754989584960455137290991372839023/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-410284570485187399163706027782063006250000000000)
      constant := (12815396673872488251413531796076154869512436397288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107064433311327764023/20000000000000000000)
  centralHi := (133830541639159705029/25000000000000000000)
  directionLo := (26882230818079713157/5000000000000000000)
  directionHi := (537644616361594263141/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree117.table
  base := (9068976549758862447175016290641759419939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-218851332429424517279801729268425000000000000)
      constant := (6895091807353187573748732800462763511053043255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree117.table
  base := (45344882747609177932555149856776821180819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1103518430563827156267190143892871206250000000000)
      constant := (34776025686326047452549080909085251397460989098411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26882230818079713157/5000000000000000000)
  centralHi := (537644616361594263141/100000000000000000000)
  directionLo := (33747317312264684087/6250000000000000000)
  directionHi := (539957076996234945393/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree118.table
  base := (9369565895768817144088843114089650980411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-220720757877167063578825387477625000000000000)
      constant := (7015426967063034786184260698847989148019872495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree118.table
  base := (11711957369459572720116792327819677499657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-834708504875365936073373160275180796875000000000)
      constant := (26537206406382641458151970449540841518629109186099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33747317312264684087/6250000000000000000)
  centralHi := (539957076996234945393/100000000000000000000)
  directionLo := (67782459532088539529/12500000000000000000)
  directionHi := (542259676256708316233/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree119.table
  base := (48371992509916009088547021107204014420083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-222590183324909609877849045686825000000000000)
      constant := (7136809344353713430781741518549836076506013147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree119.table
  base := (48371992509062476300015740653862287941657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3367112747311446019785414850522832756250000000000)
      constant := (107985419090596467365786235114766461841152513280099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67782459532088539529/12500000000000000000)
  centralHi := (542259676256708316233/100000000000000000000)
  directionLo := (544552539237255079057/100000000000000000000)
  directionHi := (272276269618627539529/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree120.table
  base := (49917371841201029826665183335015693477433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-224459608772652156176872703896025000000000000)
      constant := (7259238939222950879030702313496059082978109297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree120.table
  base := (9983474368095351964678610758522943559263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1131797158373809431759112353314980775000000000000)
      constant := (36612619151380550412638607475266955855883127977235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544552539237255079057/100000000000000000000)
  centralHi := (272276269618627539529/50000000000000000000)
  directionLo := (136708947102378405387/25000000000000000000)
  directionHi := (546835788409513621549/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree121.table
  base := (12870991868004921067883656785154766049261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-56582258555098675618974090526306250000000000)
      constant := (1845678937917209629375258574173374737832374149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree121.table
  base := (51483967471405143401617068462262926895281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3423670202931410570769259269367051893750000000000)
      constant := (111706140716137400709144875826903368633651410287467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136708947102378405387/25000000000000000000)
  centralHi := (546835788409513621549/100000000000000000000)
  directionLo := (274554771849428284363/50000000000000000000)
  directionHi := (549109543698856568727/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree122.table
  base := (26535889700900759293390707925471990200743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-114099229834068624387460010157212500000000000)
      constant := (3753619890844886970683181540013750820473887087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree122.table
  base := (2122871176051204720103938695495660240901/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3451948930741392846261181478789161462500000000000)
      constant := (113590268876559607708063161850930459820049165420175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274554771849428284363/50000000000000000000)
  centralHi := (549109543698856568727/100000000000000000000)
  directionLo := (275686961278947045907/50000000000000000000)
  directionHi := (110274784511578818363/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree123.table
  base := (27340403815033886524543421816488450059799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-115033942557939897536971839261812500000000000)
      constant := (3816405514642206157281943209406566056217975391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree123.table
  base := (54680807629625425930944319922600787542989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1160075886183791707251034562737090343750000000000)
      constant := (38496747311796013522102579079949908676024631505141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275686961278947045907/50000000000000000000)
  centralHi := (110274784511578818363/20000000000000000000)
  directionLo := (110725808007454289399/20000000000000000000)
  directionHi := (138407260009317861749/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree124.table
  base := (1407776303910420307816308025309157213173/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-28992163820452792671620917091603125000000000)
      constant := (969928686806453180425907009402117113059014785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree124.table
  base := (56311052156041557473109061885347696068077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3508506386361357397245025897633380600000000000000)
      constant := (117406059892605727908695761659585696865878817475039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110725808007454289399/20000000000000000000)
  centralHi := (138407260009317861749/25000000000000000000)
  directionLo := (111175001770776298997/20000000000000000000)
  directionHi := (277937504426940747493/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree125.table
  base := (7245314122563983291222811639847401468307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-29225842001420610958998874367753125000000000)
      constant := (985886897148808417604061974676018850724474363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree125.table
  base := (7245314122524193534920326483393994310597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-442098139271417459092118513381936271093750000000)
      constant := (14917215343524805034977971992344357007775330720179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111175001770776298997/20000000000000000000)
  centralHi := (277937504426940747493/50000000000000000000)
  directionLo := (558111939456606634993/100000000000000000000)
  directionHi := (279055969728303317497/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree126.table
  base := (29817595051035357806852950469006031289309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-117838080729553716985507326575612500000000000)
      constant := (4007904038750072626150632278507937941891668981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree126.table
  base := (59635190101800712645517335868108420592849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1188354613993773982742956772159199912500000000000)
      constant := (40428410167384751336223412453970265074824072031481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558111939456606634993/100000000000000000000)
  centralHi := (279055969728303317497/50000000000000000000)
  directionLo := (140084985022424661901/25000000000000000000)
  directionHi := (112067988017939729521/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree127.table
  base := (30664541760428506299213481049869871261671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-118772793453424990135019155680212500000000000)
      constant := (4072784097689997638750340381580934468374033839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree127.table
  base := (30664541760314002853532348079838896382669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-1796671284895652111860396262949854653125000000000)
      constant := (61624291577231592135111538470258268225074213883183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140084985022424661901/25000000000000000000)
  centralHi := (112067988017939729521/20000000000000000000)
  directionLo := (562559116853899354919/100000000000000000000)
  directionHi := (14063977921347483873/2500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree128.table
  base := (31522096618336489856886597139381166780349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-119707506177296263284530984784812500000000000)
      constant := (4138187765414730929618064956497321697486000341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree128.table
  base := (63044193236478756235089782179762219232619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3621621297601286499212714735321818875000000000000)
      constant := (125227780705116876370965676214034508012446806057833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562559116853899354919/100000000000000000000)
  centralHi := (14063977921347483873/2500000000000000000)
  directionLo := (564769573765399749373/100000000000000000000)
  directionHi := (282384786882699874687/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree129.table
  base := (64780519249353265911212928367878039551487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-241284437802335072868085627778825000000000000)
      constant := (8408230083848080526412286547992069413100126983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree129.table
  base := (161951298122971381704151246315051413799/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-152079167725469532279359872697663685156250000000)
      constant := (5300950964754514417707717707008370397162927664050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell150.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564769573765399749373/100000000000000000000)
  centralHi := (282384786882699874687/50000000000000000000)
  directionLo := (113394282562546058633/20000000000000000000)
  directionHi := (283485706406365146583/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree130.table
  base := (33269030779379888987721499828053272501917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-121576931625038809583554642994012500000000000)
      constant := (4270565927217731687593682039240501642457884853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree130.table
  base := (13307612311724019917249776356747846696313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3678178753221251050196559154166038012500000000000)
      constant := (129233710501431760851509696829481196099557006353455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113394282562546058633/20000000000000000000)
  centralHi := (283485706406365146583/50000000000000000000)
  directionLo := (35572795875729401747/6250000000000000000)
  directionHi := (569164734011670427953/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree131.table
  base := (68316820164777332071468672283194301263547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-245023288697820165466132944197225000000000000)
      constant := (8675080842591286854168862291429992792249303523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree131.table
  base := (17079205041164722613490289153320573621573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-926614370257808331422120340897036895312500000000)
      constant := (32815110686770564139145302827575899067918606552511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35572795875729401747/6250000000000000000)
  centralHi := (569164734011670427953/100000000000000000000)
  directionLo := (285674817729130470361/50000000000000000000)
  directionHi := (571349635458260940723/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree132.table
  base := (2191149845853437358637131592772618654819/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-30861589268195338970644575300803125000000000)
      constant := (1101259631039410186042268776554543143205546284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree132.table
  base := (1095574922925149494022595069527469261999/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-155614008701717316715850148875427381250000000000)
      constant := (5554292495460657595756014602056397398434563942648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285674817729130470361/50000000000000000000)
  centralHi := (571349635458260940723/100000000000000000000)
  directionLo := (143381553344999672251/25000000000000000000)
  directionHi := (114705242675999737801/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree133.table
  base := (899224828328475113262227841348923196253/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-31095267449163157258022532576953125000000000)
      constant := (1118265058950902904287654917933878752582746770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree133.table
  base := (71937986266192860126422910438623010529847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3763014936651197876672325782432366718750000000000)
      constant := (135361441933348970606040815988067303480697676692429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143381553344999672251/25000000000000000000)
  centralHi := (114705242675999737801/20000000000000000000)
  directionLo := (575694562185289280889/100000000000000000000)
  directionHi := (57569456218528928089/10000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree134.table
  base := (73780393761615198434091810720374176029809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-250631565041047804363203918824825000000000000)
      constant := (9083211112466926208193398012713731060467733481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree134.table
  base := (73780393761543007985307716602017671228833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3791293664461180152164247991854476287500000000000)
      constant := (137435708873959027962317885329699005289728888858331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575694562185289280889/100000000000000000000)
  centralHi := (57569456218528928089/10000000000000000000)
  directionLo := (115570954902245923503/20000000000000000000)
  directionHi := (144463693627807404379/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree135.table
  base := (37822008776633398130435068863532530145557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-126250495244395175331113788517012500000000000)
      constant := (4610674485447118284285503892505912877178869613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree135.table
  base := (37822008776602797798312443760378599874661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4459464331693922520973641381487425000000000000)
      linear := (-636595398711860404609361700212764309375000000000)
      constant := (23254303452147273794134347735184109086118734827709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115570954902245923503/20000000000000000000)
  centralHi := (144463693627807404379/25000000000000000000)
  directionLo := (116001388253957744787/20000000000000000000)
  directionHi := (18125216914680897623/3125000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree136.table
  base := (38764428820593805274872982110076871595467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-127185207968266448480625617621612500000000000)
      constant := (4680267023444513685564878135833205932311666803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree136.table
  base := (19382214410283932375029648962103449952487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-961962780020286175787023102674673856250000000000)
      constant := (35407944362530226979138191834225883434180773670909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116001388253957744787/20000000000000000000)
  centralHi := (18125216914680897623/3125000000000000000)
  directionLo := (582151151692452005617/100000000000000000000)
  directionHi := (291075575846226002809/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree137.table
  base := (79434914025340484039996048502972460644697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-256239841384275443260274893452425000000000000)
      constant := (9500766340451194241124271886751549641950953873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree137.table
  base := (19858728506324126447550901445047537438823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-969032461972781744660003655030201248437500000000)
      constant := (35938394771417313930234596789598324923399166898261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582151151692452005617/100000000000000000000)
  centralHi := (291075575846226002809/50000000000000000000)
  directionLo := (116857498674678192043/20000000000000000000)
  directionHi := (73035936671673870027/12500000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree138.table
  base := (20340546676423749629960587146708811150509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-64527316708004497389824637915406250000000000)
      constant := (2410511462895162933449417527580255050521779781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree138.table
  base := (81362186705657721255139118855314006962973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1301469525233703084710645609847638187500000000000)
      constant := (48630408539842467710071722801458509303069124422437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116857498674678192043/20000000000000000000)
  centralHi := (73035936671673870027/12500000000000000000)
  directionLo := (146604013077804359103/25000000000000000000)
  directionHi := (586416052311217436413/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree139.table
  base := (83310675682226385224541920210103680109371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-259978692279760535858322209870825000000000000)
      constant := (9784372580277330273689788011943881237427223139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree139.table
  base := (83310675682194789568835476591441162973761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-3932687303511091529623859038965024131250000000000)
      constant := (148044717051694305704785555055063385859693432476827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146604013077804359103/25000000000000000000)
  centralHi := (586416052311217436413/100000000000000000000)
  directionLo := (588536912949378753277/100000000000000000000)
  directionHi := (294268456474689376639/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree140.table
  base := (21320095238728652155775712872379961544067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-65462029431875770539336467020006250000000000)
      constant := (2481936631635293395248517327785015311977284203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree140.table
  base := (21320095238721957499560774348574522044309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-990241507830268451278945312096783425000000000000)
      constant := (37553513345542279725257517307048566427631172784663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588536912949378753277/100000000000000000000)
  centralHi := (294268456474689376639/50000000000000000000)
  directionLo := (36915634888452960297/6250000000000000000)
  directionHi := (590650158215247364753/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree141.table
  base := (87271302523743596085132410395073631187359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-263717543175245628456369526289225000000000000)
      constant := (10072167690372136507691740823637261830005291431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree141.table
  base := (5454456407732556328064637347863862990799/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-166218531630460670025320977408718469531250000000)
      constant := (6349968108789631896861809602003671557401720132562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36915634888452960297/6250000000000000000)
  centralHi := (590650158215247364753/100000000000000000000)
  directionLo := (148188967389489066437/25000000000000000000)
  directionHi := (592755869557956265749/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree142.table
  base := (89283440388700590280624341567441930133521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-265586968622988174755393184498425000000000000)
      constant := (10217636071770183218442814978131144381745060489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree142.table
  base := (44641720194340678706964730303709646108163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42135000000000000000000000000000000000000000
      center := (741576)
      previous := (370788)
      next := (370788)
      square := (2653916483848793406649657636275000000000000)
      linear := (-398484773550985752439954936245918750000000000)
      constant := (15334284937317983373456946871580167047128489601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148188967389489066437/25000000000000000000)
  centralHi := (592755869557956265749/100000000000000000000)
  directionLo := (594854126985028980261/100000000000000000000)
  directionHi := (297427063492514490131/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree143.table
  base := (5707299659360975302215837029457181999691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-33432049258841340131802105338453125000000000)
      constant := (1295518958841910707690296742531252948474264038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree143.table
  base := (45658397274879653320629830443477675464133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2022901107375510315795773938326731203125000000000)
      constant := (78408565881717463614842257730296573853440798905431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594854126985028980261/100000000000000000000)
  centralHi := (297427063492514490131/50000000000000000000)
  directionLo := (596945009097850740081/100000000000000000000)
  directionHi := (298472504548925370041/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree144.table
  base := (93371365006960966853551994776711246218047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-269325819518473267353440500916825000000000000)
      constant := (10511714487267422283765363910554981890626494023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree144.table
  base := (93371365006947156215334845720050616972713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1358026980853667635694490028691857325000000000000)
      constant := (53016615895711966519248715235738460499887884468497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596945009097850740081/100000000000000000000)
  centralHi := (298472504548925370041/50000000000000000000)
  directionLo := (599028593126025347701/100000000000000000000)
  directionHi := (299514296563012673851/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree145.table
  base := (46605054570435025642290591815488517171/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-33899405620776976706558019890753125000000000)
      constant := (1332540565170822118847848007731322554651734784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree145.table
  base := (95447151760239230326763509998466525273859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4102359670370985182575392295497681543750000000000)
      constant := (161298408509142584244117242600646881426122781666513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599028593126025347701/100000000000000000000)
  centralHi := (299514296563012673851/50000000000000000000)
  directionLo := (60110495496066021203/10000000000000000000)
  directionHi := (601104954960660212031/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree146.table
  base := (97544154809641364149272183037824258674831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-273064670413958359951487817335225000000000000)
      constant := (10809981773032738039854664427136248342617600279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree146.table
  base := (24386038702407862246825435538270978218817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-1032659599545241864516828626229947778125000000000)
      constant := (40890703557363701992207162684442074975113490600219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60110495496066021203/10000000000000000000)
  centralHi := (601104954960660212031/100000000000000000000)
  directionLo := (603174169186620144051/100000000000000000000)
  directionHi := (150793542296655036013/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree147.table
  base := (99662374155129459011456251664541316950013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-274934095861700906250511475544425000000000000)
      constant := (10960686242265897678074010987235396559312586517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree147.table
  base := (797298993240968467001160048774407975759/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1386305708663649911186412238113966893750000000000)
      constant := (55281021616024151249377975256899919009469730408875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603174169186620144051/100000000000000000000)
  centralHi := (150793542296655036013/25000000000000000000)
  directionLo := (302618154556894347789/50000000000000000000)
  directionHi := (605236309113788695579/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree148.table
  base := (25450452449178380390164792080084633766639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-69200880327360863137383783438406250000000000)
      constant := (2778109482266512775666325082436857736250488951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree148.table
  base := (101801809796706404437520238102042161921751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4187195853800932009051158923764010250000000000000)
      constant := (168139160364995451317032663196350530776937076807757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302618154556894347789/50000000000000000000)
  centralHi := (605236309113788695579/100000000000000000000)
  directionLo := (607291446807374112261/100000000000000000000)
  directionHi := (303645723403687056131/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree149.table
  base := (103962461734392772313961320869068847579127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-278672946757185998848558791962825000000000000)
      constant := (11265236833433196124061011264181914392849767743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree149.table
  base := (103962461734386742874034979827851482207413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4215474581610914284543081133186119818750000000000)
      constant := (170451100780223769057266831085420434565145820898391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607291446807374112261/100000000000000000000)
  centralHi := (303645723403687056131/50000000000000000000)
  directionLo := (609339653117295346471/100000000000000000000)
  directionHi := (76167456639661918309/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree150.table
  base := (21228865993633437493734009288239225196373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-280542372204928545147582450172025000000000000)
      constant := (11419082955367332675399380100538319917883058785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree150.table
  base := (106144329968162079715235094613598172591823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1414584436473632186678334447536076462500000000000)
      constant := (57592962031252469075005691733106195232147631698087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609339653117295346471/100000000000000000000)
  centralHi := (76167456639661918309/12500000000000000000)
  directionLo := (611380997706682031981/100000000000000000000)
  directionHi := (305690498853341015991/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree151.table
  base := (108347414498037364396669482894844168790077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-282411797652671091446606108381225000000000000)
      constant := (11573976294868462434698029382060117270131326293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree151.table
  base := (54173707249016518814406231450130836078909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2136016018615439417763462776015169478125000000000)
      constant := (87561258152798196135761319569480587159821415076863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611380997706682031981/100000000000000000000)
  centralHi := (305690498853341015991/50000000000000000000)
  directionLo := (613415549079520855643/100000000000000000000)
  directionHi := (153353887269880213911/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree152.table
  base := (13821464415500551111781227830630911827447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-35535152887551704718203720823803125000000000)
      constant := (1466239606492073563517342282405142231323298623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree152.table
  base := (55285857662000371929159783952359208803259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2150155382520430555509423880726224262500000000000)
      constant := (88740995707870386041330572436255051211081305572313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613415549079520855643/100000000000000000000)
  centralHi := (153353887269880213911/25000000000000000000)
  directionLo := (61544337460747936729/10000000000000000000)
  directionHi := (615443374607479367291/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree153.table
  base := (112817232446069840723609014825249522092429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-286150648548156184044653424799625000000000000)
      constant := (11886904626571715164733520771197225907557633061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree153.table
  base := (112817232446066736349170592235683279654609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1442863164283614462170256656958186031250000000000)
      constant := (59952437141396870663711175067391386776828837568921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61544337460747936729/10000000000000000000)
  centralHi := (615443374607479367291/100000000000000000000)
  directionLo := (617464540555936943797/100000000000000000000)
  directionHi := (308732270277968471899/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree154.table
  base := (115083965864235514531874440425536763665981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-288020073995898730343677083008825000000000000)
      constant := (12044939618773847614186157731129532769137740629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree154.table
  base := (23016793172846577032712104856459626006651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4356868220660825662002692180296667662500000000000)
      constant := (182248476330945991438129944767583208050683349260285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617464540555936943797/100000000000000000000)
  centralHi := (308732270277968471899/50000000000000000000)
  directionLo := (619479112109251362811/100000000000000000000)
  directionHi := (154869778027312840703/25000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree155.table
  base := (117371915578503553695996882097931445807291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-289889499443641276642700741218025000000000000)
      constant := (12204021828542991821062503887507589431272680419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree155.table
  base := (58685957789250663373028729466310263770333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2192573474235403968747307194859388615625000000000)
      constant := (92327743068003500590449416817803019462841696148831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619479112109251362811/100000000000000000000)
  centralHi := (154869778027312840703/25000000000000000000)
  directionLo := (310743576697644121251/50000000000000000000)
  directionHi := (621487153395288242503/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree156.table
  base := (23936216317775259006207792241424648662771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-291758924891383822941724399427225000000000000)
      constant := (12364151255879154349476070143744809190468618695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree156.table
  base := (23936216317774881797754060216749267693539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1471141892093596737662178866380295600000000000000)
      constant := (62359446946457913653029119795162022727708762240455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310743576697644121251/50000000000000000000)
  centralHi := (621487153395288242503/100000000000000000000)
  directionLo := (311744363754619731237/50000000000000000000)
  directionHi := (24939549100369578499/4000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree157.table
  base := (4880458555814249705073604599006658834947/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-293628350339126369240748057636425000000000000)
      constant := (12525327900782342233415215478997942616684153075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree157.table
  base := (122011463895354645370735680445391093567999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4441704404090772488478458808562996368750000000000)
      constant := (189517040441046317546559331918863274395201473995493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311744363754619731237/50000000000000000000)
  centralHi := (24939549100369578499/4000000000000000000)
  directionLo := (312741948268377797277/50000000000000000000)
  directionHi := (125096779307351118911/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree158.table
  base := (124363062497946029353572480647876980983623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-295497775786868915539771715845625000000000000)
      constant := (12687551763252562868612253426790486439582997007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree158.table
  base := (485793212882596393438440193312228458603/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-558747891487594345496297627248138242187500000000)
      constant := (23996448117628105390879910858179387432795930205072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312741948268377797277/50000000000000000000)
  centralHi := (125096779307351118911/20000000000000000000)
  directionLo := (627472721576416337563/100000000000000000000)
  directionHi := (156868180394104084391/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree159.table
  base := (126735877396648384808538504887826729169439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (176)
      previous := (88)
      next := (88)
      square := (629860326058809399940585650000000000000)
      linear := (-105862300190320919130934629425000000000000)
      constant := (4574874632712646465826275030187826729169439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree159.table
  base := (126735877396647239379394951215848315174017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3175125903662458185100492261650000000000000)
      linear := (-533791605519252051674653284372518750000000000)
      constant := (23073688660176745454103164407263661864604719697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627472721576416337563/100000000000000000000)
  centralHi := (156868180394104084391/25000000000000000000)
  directionLo := (629455262761561964567/100000000000000000000)
  directionHi := (78681907845195245571/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree160.table
  base := (6456495429573305433581433158515032123743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-74809156670588502034454758066006250000000000)
      constant := (3253785285223533314849321805907343626177970435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree160.table
  base := (129129908591465138744280414252919598706997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4526540587520719314954225436829325075000000000000)
      constant := (196928208635900209165271467693676526533309777007479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629455262761561964567/100000000000000000000)
  centralHi := (78681907845195245571/12500000000000000000)
  directionLo := (157857894820376962999/25000000000000000000)
  directionHi := (631431579281507851997/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree161.table
  base := (131545156082402048600985327342623094036733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-301106052130096554436842690473225000000000000)
      constant := (13180506656065498878357817340804928271149182997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree161.table
  base := (131545156082401227317241030207258493498799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (7476569232)
      previous := (3738284616)
      next := (3738284616)
      square := (26756785990163535125841848288924550000000000000)
      linear := (-4554819315330701590446147646251434643750000000000)
      constant := (199430287830797289973417380319128198187596122911093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157857894820376962999/25000000000000000000)
  centralHi := (631431579281507851997/100000000000000000000)
  directionLo := (63340172940216326477/10000000000000000000)
  directionHi := (633401729402163264771/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree162.table
  base := (26796323973891816387702316429333791067383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-302975477577839100735866348682425000000000000)
      constant := (13346919388803928861841002676364193095541394235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree162.table
  base := (8373851241841149159075514199466737761847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114866082923480630243410345371856250000000000)
      linear := (-190962418464195161080752910653064342187500000000)
      constant := (8414508830166699948812151874867638071942401794286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63340172940216326477/10000000000000000000)
  centralHi := (633401729402163264771/100000000000000000000)
  directionLo := (127073154097214943609/20000000000000000000)
  directionHi := (317682885243037359023/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree163.table
  base := (68219649976320050305524591564009732977017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-152422451512790823517445003445812500000000000)
      constant := (6757189669554715666634670860817353339932440753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree163.table
  base := (68219649976319755916749534626229933774667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2305688385475333070714996032547826890625000000000)
      constant := (102240990457755429278890050551613090500460996666169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127073154097214943609/20000000000000000000)
  centralHi := (317682885243037359023/50000000000000000000)
  directionLo := (127464751802382684411/20000000000000000000)
  directionHi := (79665469876489177757/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree164.table
  base := (27783639266389599742160226019787120979691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-306714328473324193333913665100825000000000000)
      constant := (13682886506982014422147832703089110114159760095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree164.table
  base := (17364774541493437527716023614604163379227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53100633750000000000000000000000000000000000000
      center := (934571154)
      previous := (467285577)
      next := (467285577)
      square := (3344598248770441890730231036115568750000000000)
      linear := (-579956937345081052115239284314720418750000000000)
      constant := (25878949350665949049999297164085675065051021228089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127464751802382684411/20000000000000000000)
  centralHi := (79665469876489177757/12500000000000000000)
  directionLo := (499434180151113703/78125000000000000)
  directionHi := (639275750593425539841/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree165.table
  base := (28283661801477132464162840240532252972909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-308583753921066739632937323310025000000000000)
      constant := (13852440892421686235483754020531775493004506905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree165.table
  base := (141418309007385240290250033186228914216733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1555978075523543564137945494646624306250000000000)
      constant := (69865684531150374335497480257845100981003254407877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499434180151113703/78125000000000000)
  centralHi := (639275750593425539841/100000000000000000000)
  directionLo := (320610899998931623213/50000000000000000000)
  directionHi := (641221799997863246427/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree166.table
  base := (7196981898947798061026233108653583834209/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442319413974798901108276272712500000000000)
      linear := (-77613294842202321482990245379806250000000000)
      constant := (3505760623857113708621885536102289584951465405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree166.table
  base := (14393963797895560393434162034067819660343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2348106477190306483952879346680991243750000000000)
      constant := (106089178639940786188420855063879947341764067169505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320610899998931623213/50000000000000000000)
  centralHi := (641221799997863246427/100000000000000000000)
  directionLo := (160790490290978467597/25000000000000000000)
  directionHi := (643161961163913870389/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree167.table
  base := (9155136452916358885285986453504254609913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221159706987399450554138136356250000000000)
      linear := (-39040325602068979028873079966053125000000000)
      constant := (1774336414500291026961623752605249402398491234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree167.table
  base := (14648218324666143970120682764636945901493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3738284616)
      previous := (1869142308)
      next := (1869142308)
      square := (13378392995081767562920924144462275000000000000)
      linear := (-2362245841095297621698840451392046028125000000000)
      constant := (107387752932309530759385809756996314444115442234755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160790490290978467597/25000000000000000000)
  centralHi := (643161961163913870389/100000000000000000000)
  directionLo := (645096287219143723119/100000000000000000000)
  directionHi := (8063703590239296539/1250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree168.table
  base := (74522972405252911738540124406328357744263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884638827949597802216552545425000000000000)
      linear := (-157096015132147189265004148968812500000000000)
      constant := (7183693677071657147886265090100176356903634767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree168.table
  base := (149045944810505567433563709668460625121187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8918928663387845041947282762974850000000000000)
      linear := (-1584256803333525839629867704068733875000000000000)
      constant := (72462833115887903406876830716071692896561653400603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell150.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645096287219143723119/100000000000000000000)
  centralHi := (8063703590239296539/1250000000000000000)
  directionLo := (129404966099394515139/20000000000000000000)
  directionHi := (40439051906060785981/6250000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree169.table
  base := (151630922670490990744689456955966504485619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1769277655899195604433105090850000000000000)
      linear := (-316061455712036924829031956146825000000000000)
      constant := (14541130609851420899439066399784009911100103771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree169.table
  base := (7581546133524538700226213350605764975587/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1869142308)
      previous := (934571154)
      next := (934571154)
      square := (6689196497540883781460462072231137500000000000)
      linear := (-1195262284452639948595381330407077798437500000000)
      constant := (55004334432253909217550267620979725207200376288045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell150.Kernel169
