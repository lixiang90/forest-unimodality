import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell087.Parameters
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch000_049
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch050_099
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch100_149
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch150_199
import ForestUnimodality.BinomialMassData.Q53_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_103.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree000.table
  base := (749304940723826854897993141/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (28845263826224815106868959600000000000)
      linear := (-1038892779276219362205591080000000000)
      constant := (29972197628953074195919725640000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree000.table
  base := (749304940723826854897993141/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (28845263826224815106868959600000000000)
      linear := (-1038892779276219362205591080000000000)
      constant := (29972197628953074195919725640000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree001.table
  base := (102345001862706216209380487580248018429981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-21147820808453170691293128368157438000000000000)
      constant := (11302047935706419111988455495754779127281246335316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree001.table
  base := (40859428788501891607492786930864198805459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-1629771019750319712752172083402600000000000)
      constant := (867388848343282808063449329245187170254229062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9995757418433980889/20000000000000000000)
  directionHi := (24989393546084952223/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree002.table
  base := (236726679525393764279650372796192617323961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-41578961199371766118419373233518883000000000000)
      constant := (6553951578919969119608911362168356449170935749649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree002.table
  base := (235931382433614612919083273605436965326049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-16022169860119661847180742939833000000000000)
      constant := (2511382236631107423096987956517006765144053841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9995757418433980889/20000000000000000000)
  centralHi := (24989393546084952223/50000000000000000000)
  directionLo := (17670169634176015221/25000000000000000000)
  directionHi := (14136135707340812177/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree003.table
  base := (18358150752542905395743484010433218514743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-6890011287810040171727290899875592000000000000)
      constant := (455655911146194112321462407581475148820364421944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree003.table
  base := (73123868382181315783955899336142295674209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-23895484621487725130600625462653000000000000)
      constant := (1570198515879048063184266150433386229615366562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17670169634176015221/25000000000000000000)
  centralHi := (14136135707340812177/20000000000000000000)
  directionLo := (8656579854430586351/10000000000000000000)
  directionHi := (86565798544305863511/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree004.table
  base := (19660329724444877427999192380659907897549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-16488248396241791394534372592848354600000000000)
      constant := (559583738525399724409993099157262035864138183941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree004.table
  base := (2446514076004976308389049964561659964557/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-6353759876571157682804101597094600000000000)
      constant := (214236076659364967326376647627703604511881704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8656579854430586351/10000000000000000000)
  centralHi := (86565798544305863511/100000000000000000000)
  directionLo := (99957574184339808891/100000000000000000000)
  directionHi := (24989393546084952223/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree005.table
  base := (17653891279065313472802035530128119466479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-102872382372127552399798107829603218000000000000)
      constant := (2081516189595216667977518164818758066969386897244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree005.table
  base := (70305244002466398682900692056126580466737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-39642114144223851697440390508293000000000000)
      constant := (797218714387340574836175299434411892171612833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/100000000000000000000)
  centralHi := (24989393546084952223/25000000000000000000)
  directionLo := (111755965371080953601/100000000000000000000)
  directionHi := (55877982685540476801/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree006.table
  base := (26848911434413225878563118588824126029467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-13700391418116238647436039188329407000000000000)
      constant := (185860466038432577832824868541621170460943702934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree006.table
  base := (53474407068218132411985371307360162935049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-47515428905591914980860273031113000000000000)
      constant := (641084393418115454055170269220401968577934841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111755965371080953601/100000000000000000000)
  centralHi := (55877982685540476801/50000000000000000000)
  directionLo := (24484505267802896177/20000000000000000000)
  directionHi := (61211263169507240443/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree007.table
  base := (2126041360773177297524667782317269974931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-28746932630792948650810119512065221600000000000)
      constant := (286574242891933075595240540913515705499703153516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree007.table
  base := (1323518603145212181870563270597778499771/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-55388743666959978264280155553933000000000000)
      constant := (549568437746559091864186601614789627330257248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24484505267802896177/20000000000000000000)
  centralHi := (61211263169507240443/50000000000000000000)
  directionLo := (33057860368631640473/25000000000000000000)
  directionHi := (132231441474526561893/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree008.table
  base := (17276474799028229354557245087590570388713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-164165803544883338681176842425687553000000000000)
      constant := (1292039468719221127605145935287495709242560040834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree008.table
  base := (21512199735920137742020407580362934787/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-2530482337133121661908001523070120000000000)
      constant := (19837324002976054856164764911979864009938112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33057860368631640473/25000000000000000000)
  centralHi := (132231441474526561893/100000000000000000000)
  directionLo := (17670169634176015221/12500000000000000000)
  directionHi := (141361357073408121769/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree009.table
  base := (1780941736407670235095635919600019691291/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-20510771548422437123144787476783222000000000000)
      constant := (134933440722798752038378284411125390701286356656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree009.table
  base := (28384162950737043772345321699231352477063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-71135373189696104831119920599573000000000000)
      constant := (466481981600762444629194278011642418429161367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17670169634176015221/12500000000000000000)
  centralHi := (141361357073408121769/100000000000000000000)
  directionLo := (18742045159563714167/12500000000000000000)
  directionHi := (149936361276509713337/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree010.table
  base := (23660700437744750613004201249020251413983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-205028084326720529535429332156410443000000000000)
      constant := (1181012935788377528026913201280398613699709627847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree010.table
  base := (1472824943954354846448005569581728402443/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-79008687951064168114539803122393000000000000)
      constant := (453986891426768993518027606620510905944284592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18742045159563714167/12500000000000000000)
  centralHi := (149936361276509713337/100000000000000000000)
  directionLo := (158046801903880644537/100000000000000000000)
  directionHi := (79023400951940322269/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree011.table
  base := (4917771231447216420733894099039340177827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-225459224717639124962555577021771888000000000000)
      constant := (1181423796928781876463505823145850175509079353772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree011.table
  base := (19586925374207030353525539021592032494889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-86882002712432231397959685645213000000000000)
      constant := (454462000023324481979044127186252872738277401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158046801903880644537/100000000000000000000)
  centralHi := (79023400951940322269/50000000000000000000)
  directionLo := (165760884261785173367/100000000000000000000)
  directionHi := (20720110532723146671/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree012.table
  base := (254760768467054113666218255862790756519/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-27321151678728635598853535765237037000000000000)
      constant := (134391176904169588354263168443098687625792673216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree012.table
  base := (1622953935116220897306425111749387739527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-18951063494760058936275913633606600000000000)
      constant := (93115084719483271946284880735249709057283886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165760884261785173367/100000000000000000000)
  centralHi := (20720110532723146671/12500000000000000000)
  directionLo := (173131597088611727021/100000000000000000000)
  directionHi := (86565798544305863511/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree013.table
  base := (13422520481907487833676896329358631501471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-266321505499476315816808066752494778000000000000)
      constant := (1261467954933617603926936225132393994004274287239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree013.table
  base := (13354987991820883949651404814888483569497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-102628632235168357964799450690853000000000000)
      constant := (485862557423131905617491342492300922188793673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173131597088611727021/100000000000000000000)
  centralHi := (86565798544305863511/50000000000000000000)
  directionLo := (2815641867911193181/1562500000000000000)
  directionHi := (36040215909263272717/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree014.table
  base := (10930700212457087178608636931862927107043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-286752645890394911243934311617856223000000000000)
      constant := (1334675398014544641165781216108497659358088505387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree014.table
  base := (135873570010828284088570031451581431103/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-22100389399307284249643866642734600000000000)
      constant := (102866534531771053481700863304189638441147632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815641867911193181/1562500000000000000)
  centralHi := (36040215909263272717/20000000000000000000)
  directionLo := (187003497905419637467/100000000000000000000)
  directionHi := (46750874476354909367/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree015.table
  base := (8761415940347661145726833342433134673581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-34131531809034834074562284053690852000000000000)
      constant := (158585744943164322139354311656421628967334019581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree015.table
  base := (2176667611647460297330165924582734660951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-118375261757904484531639215736493000000000000)
      constant := (550269006892890924937329396594987928072116636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187003497905419637467/100000000000000000000)
  centralHi := (46750874476354909367/25000000000000000000)
  directionLo := (193567010071620251263/100000000000000000000)
  directionHi := (1512242266184533213/781250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree016.table
  base := (343149131924145904166152153562919635497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-65522985334446420419637360269715822600000000000)
      constant := (307566135450512012497658272818092335552723749892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree016.table
  base := (1703445617345429747570356404765737191547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-126248576519272547815059098259313000000000000)
      constant := (593124559452837445432455181179886823460488492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193567010071620251263/100000000000000000000)
  centralHi := (1512242266184533213/781250000000000000)
  directionLo := (99957574184339808891/50000000000000000000)
  directionHi := (199915148368679617783/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree017.table
  base := (324653638224387185764874026829149577553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (68854365884794289280473878289190000000000000)
      linear := (-1204311650737545666177553793127822000000000000)
      constant := (5762015777720952975998064021780976618029407888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree017.table
  base := (2575171321115712227633475498102337065703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-134121891280640611098478980782133000000000000)
      constant := (642465644741140734896979426649656387860086254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/50000000000000000000)
  centralHi := (199915148368679617783/100000000000000000000)
  directionLo := (20606781822127305159/10000000000000000000)
  directionHi := (206067818221273051591/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree018.table
  base := (1861284353415567453668008533132952879013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-40941911939341032550271032342144667000000000000)
      constant := (200947687806753082888234579275175154320013474026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree018.table
  base := (3683111843534944760890186418420203915687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-141995206042008674381898863304953000000000000)
      constant := (697939628916703821287588883363433943341523383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20606781822127305159/10000000000000000000)
  centralHi := (206067818221273051591/100000000000000000000)
  directionLo := (212042035610112182653/100000000000000000000)
  directionHi := (106021017805056091327/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree019.table
  base := (2419831924458160427569585743446554269297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-388908347844987888379565535944663448000000000000)
      constant := (1966992224683652620091960108948353452150969841673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree019.table
  base := (298078927171235524937242278181078819943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-149868520803376737665318745827773000000000000)
      constant := (759255203098846008541790819779511521606202296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212042035610112182653/100000000000000000000)
  centralHi := (106021017805056091327/50000000000000000000)
  directionLo := (108926241127751824209/50000000000000000000)
  directionHi := (217852482255503648419/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree020.table
  base := (631662461013344917236123433991310545261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-409339488235906483806691780810024893000000000000)
      constant := (2139979127149857762968268858011608243215453882698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree020.table
  base := (307999665577441193832622327563310621427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-157741835564744800948738628350593000000000000)
      constant := (826169392528133791602570397109336649530876172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108926241127751824209/50000000000000000000)
  centralHi := (217852482255503648419/100000000000000000000)
  directionLo := (223511930742161907203/100000000000000000000)
  directionHi := (55877982685540476801/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree021.table
  base := (233815113467585707153547606594137310047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-47752292069647231025979780630598482000000000000)
      constant := (258551021500700902445416613018970866711741412047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree021.table
  base := (206001274630862354972151812686150535083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-165615150326112864232158510873413000000000000)
      constant := (898478373874362181138520582844600371026695547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223511930742161907203/100000000000000000000)
  centralHi := (55877982685540476801/25000000000000000000)
  directionLo := (114515787495975233007/50000000000000000000)
  directionHi := (45806314998390093203/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree022.table
  base := (-85611215352594734606846403536133693173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-450201769017743674660944270540747783000000000000)
      constant := (2527485615444398988974359640189598096363047995544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree022.table
  base := (-14190631811564621383378788255576955157/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-6939538603499237100623135735849320000000000)
      constant := (39040423625754641983883971186256608165478774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114515787495975233007/50000000000000000000)
  centralHi := (45806314998390093203/20000000000000000000)
  directionLo := (23442129063397351571/10000000000000000000)
  directionHi := (234421290633973515711/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree023.table
  base := (-753224833276340911599243226048043920281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-470632909408662270088070515406109228000000000000)
      constant := (2741181456601552123485641510811247527887741606942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree023.table
  base := (-1528237538637188125694023066590687437859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-181361779848848990798998275919053000000000000)
      constant := (1058621361481808990061475946171718396971753869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23442129063397351571/10000000000000000000)
  centralHi := (234421290633973515711/100000000000000000000)
  directionLo := (239689842633563277601/100000000000000000000)
  directionHi := (119844921316781638801/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree024.table
  base := (-1121201102923795153556840391826479166167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-54562672199953429501688528919052297000000000000)
      constant := (329747594602973699295165898374183984100105623666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree024.table
  base := (-565407724315704748169278774252560342907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-189235094610217054082418158441873000000000000)
      constant := (1146188530885443363352463347195410349288398548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239689842633563277601/100000000000000000000)
  centralHi := (119844921316781638801/50000000000000000000)
  directionLo := (244845052678028961771/100000000000000000000)
  directionHi := (61211263169507240443/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree025.table
  base := (-1814061702048372455422768786434433209/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 11037603600000000000000000000000000000000000000
      center := (165564054)
      previous := (82782027)
      next := (82782027)
      square := (795956469628221984082278033023036400000000000)
      linear := (-20459807607619978437692920205473284720000000000)
      constant := (128274288807263228002128069062955808140741127616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree025.table
  base := (-291943971981701554106873825652552671293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-39421681874317023473167608192938600000000000)
      constant := (247721778787330571722229477369269137420505126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244845052678028961771/100000000000000000000)
  centralHi := (61211263169507240443/25000000000000000000)
  directionLo := (62473483865212380557/25000000000000000000)
  directionHi := (249893935460849522229/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree026.table
  base := (-3494984268340280650529588325016465919121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-531926330581418056369449250002193563000000000000)
      constant := (3458340548895946064114962856016339417279581853911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree026.table
  base := (-3509886040847325346503199579336285278113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-204981724132953180649257923487513000000000000)
      constant := (1335795223070922543607623701798699349484499183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62473483865212380557/25000000000000000000)
  centralHi := (249893935460849522229/100000000000000000000)
  directionLo := (254842810648673539091/100000000000000000000)
  directionHi := (63710702662168384773/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree027.table
  base := (-2013415923551290746226741561979897735473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-61373052330259627977397277207506112000000000000)
      constant := (413553991597523091946769437503260272751284093054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree027.table
  base := (-1009980140287304253848272702084452150491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-212855038894321243932677806010333000000000000)
      constant := (1437673778303513291896461106252095188541763924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254842810648673539091/100000000000000000000)
  centralHi := (63710702662168384773/25000000000000000000)
  directionLo := (64924348908229397633/25000000000000000000)
  directionHi := (259697395632917590533/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree028.table
  base := (-2251969728066331301564979045648186690917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-572788611363255247223701739732916453000000000000)
      constant := (3997630597256476580837083839679800970234312167494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree028.table
  base := (-1128854994420468699553221314766593972763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-220728353655689307216097688533153000000000000)
      constant := (1544182213756385117764375912802008818171829332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64924348908229397633/25000000000000000000)
  centralHi := (259697395632917590533/100000000000000000000)
  directionLo := (52892576589810624757/20000000000000000000)
  directionHi := (132231441474526561893/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree029.table
  base := (-4931296196980527610956297628108681471439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-593219751754173842650827984598277898000000000000)
      constant := (4285136898219179609991412241128685350623978991049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree029.table
  base := (-77208645335826196317115705199429179763/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-228601668417057370499517571055973000000000000)
      constant := (1655267813191334267595616210715469373241237312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52892576589810624757/20000000000000000000)
  centralHi := (132231441474526561893/50000000000000000000)
  directionLo := (134572002676010791513/50000000000000000000)
  directionHi := (269144005352021583027/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree030.table
  base := (-5313122526157462858986434430881063825147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-68183432460565826453106025495959927000000000000)
      constant := (509376485327873374559122537284868037431035472853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree030.table
  base := (-1330480558148895386553124785957736761503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-236474983178425433782937453578793000000000000)
      constant := (1770886000772919013291827256981387482788858692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134572002676010791513/50000000000000000000)
  centralHi := (269144005352021583027/100000000000000000000)
  directionLo := (6843627271782371093/2500000000000000000)
  directionHi := (273745090871294843721/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree031.table
  base := (-5652988767491267974438072242726677507511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-634082032536011033505080474329000788000000000000)
      constant := (4895286486903681646595513660938383784942643898401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree031.table
  base := (-2830339867074801686127416033515248032509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-244348297939793497066357336101613000000000000)
      constant := (1890999083114979013870473389004316467246224038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6843627271782371093/2500000000000000000)
  centralHi := (273745090871294843721/100000000000000000000)
  directionLo := (69567527417313173037/25000000000000000000)
  directionHi := (278270109669252692149/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree032.table
  base := (-5953915304919581623568311633492073889439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-654513172926929628932206719194362233000000000000)
      constant := (5217747910576084779886198287814148827666155229049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree032.table
  base := (-5960630238458768634785324844463431390383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-252221612701161560349777218624433000000000000)
      constant := (2015575186195202973013176378509503456379426753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69567527417313173037/25000000000000000000)
  centralHi := (278270109669252692149/100000000000000000000)
  directionLo := (282722714146816243537/100000000000000000000)
  directionHi := (141361357073408121769/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree033.table
  base := (-6218457311511690129322628136604505898313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-74993812590872024928814773784413742000000000000)
      constant := (616855792388822147387246928645826227436266443687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree033.table
  base := (-6224314353051427192370086217450010653289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-260094927462529623633197101147253000000000000)
      constant := (2144587356708322627070408377860281836979256999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282722714146816243537/100000000000000000000)
  centralHi := (141361357073408121769/50000000000000000000)
  directionLo := (287106273448956212003/100000000000000000000)
  directionHi := (71776568362239053001/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree034.table
  base := (-6448776413133956841408327803713997006893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (68854365884794289280473878289190000000000000)
      linear := (-2406143438438639514832038785207907000000000000)
      constant := (20405153985294166862711046091274256851784849467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree034.table
  base := (-6453880475550024938548602747743604985701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-267968242223897686916616983670073000000000000)
      constant := (2278012802303961447557608974123010094706698091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287106273448956212003/100000000000000000000)
  centralHi := (71776568362239053001/25000000000000000000)
  directionLo := (291423903297157949159/100000000000000000000)
  directionHi := (7285597582428948729/2500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree035.table
  base := (-332335065359999154020091742064186187301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-143161318819937083042717090758089313600000000000)
      constant := (1250771912047008055767722088154131725204762081164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree035.table
  base := (-6651145346011200046474210130067929580001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-275841556985265750200036866192893000000000000)
      constant := (2415832249186858560095794428912364335085769391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291423903297157949159/100000000000000000000)
  centralHi := (7285597582428948729/2500000000000000000)
  directionLo := (147839245949913209137/50000000000000000000)
  directionHi := (11827139675993056731/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree036.table
  base := (-3406889520785801638151154551003554079103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-81804192721178223404523522072867557000000000000)
      constant := (735774401966872733668074448002441141379832245794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree036.table
  base := (-3408822624125861973909972789285092119303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-283714871746633813483456748715713000000000000)
      constant := (2558029398922001836566345490423456915412628946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147839245949913209137/50000000000000000000)
  centralHi := (11827139675993056731/4000000000000000000)
  directionLo := (299872722553019426673/100000000000000000000)
  directionHi := (149936361276509713337/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree037.table
  base := (-6951318394020520762378650370605538026027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-756668874881522606067837943521169458000000000000)
      constant := (7001383559724845814122119074052495132384968727757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree037.table
  base := (-6954679305518944485489528043276398378739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-291588186508001876766876631238533000000000000)
      constant := (2704590469110860163703896604315461689599957949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299872722553019426673/100000000000000000000)
  centralHi := (149936361276509713337/50000000000000000000)
  directionLo := (152004546717001704749/50000000000000000000)
  directionHi := (304009093434003409499/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree038.table
  base := (-1765106642453789070788896984044095687169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-777100015272441201494964188386530903000000000000)
      constant := (7392070834071872262726755486136316792845589717916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree038.table
  base := (-1412669218358842562195476665031139851697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-59892300253873988010059302752270600000000000)
      constant := (571100760996413077428448681453179437313346527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152004546717001704749/50000000000000000000)
  centralHi := (304009093434003409499/100000000000000000000)
  directionLo := (308089935002377291231/100000000000000000000)
  directionHi := (9627810468824290351/3125000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree039.table
  base := (-1428408049397396918201644362146407601093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-17722914570296884376046454072264274400000000000)
      constant := (173200124312020074049472621937023668873641260907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree039.table
  base := (-7144574591025182269693223883038211157583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-307334816030738003333716396284173000000000000)
      constant := (3010759550944916852539934259799034617829201953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308089935002377291231/100000000000000000000)
  centralHi := (9627810468824290351/3125000000000000000)
  directionLo := (156058712676490376923/50000000000000000000)
  directionHi := (312117425352980753847/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree040.table
  base := (-1799237960006892924795575114300860795309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-817962296054278392349216678117253793000000000000)
      constant := (8207165973739327019627059274843887544025985184876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree040.table
  base := (-3599575188501472630969001118789912598219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-315208130792106066617136278806993000000000000)
      constant := (3170349372847064860622176356623235634490989258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156058712676490376923/50000000000000000000)
  centralHi := (312117425352980753847/100000000000000000000)
  directionLo := (158046801903880644537/50000000000000000000)
  directionHi := (12643744152310451563/4000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree041.table
  base := (-3612915859272439508279008786887604496159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-838393436445196987776342922982615238000000000000)
      constant := (8631533474982147911340836604340334695214096177138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree041.table
  base := (-722773775177027478662029935628087371663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-64616289110694825980111232265962600000000000)
      constant := (666853244621627526528709712450857842148054466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158046801903880644537/50000000000000000000)
  centralHi := (12643744152310451563/4000000000000000000)
  directionLo := (160010191493684560211/50000000000000000000)
  directionHi := (320020382987369120423/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree042.table
  base := (-1807311750979152318564969541451526497569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-95424952981790620355941018649775187000000000000)
      constant := (1007454716512996176200625089379665732227707793724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree042.table
  base := (-7230898466487544819689142664449074526421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-330954760314842193183976043852633000000000000)
      constant := (3502504142110074761093207644737105768349199611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160010191493684560211/50000000000000000000)
  centralHi := (320020382987369120423/100000000000000000000)
  directionLo := (161949779782643468259/50000000000000000000)
  directionHi := (323899559565286936519/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree043.table
  base := (-7207677470995736998134606159917736108189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-879255717227034178630595412713338128000000000000)
      constant := (9513829655732169090278441642422146405196007760299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree043.table
  base := (-7209107552342497996189860621395019101579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-338828075076210256467395926375453000000000000)
      constant := (3675058090247005484355957714446859242351348389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161949779782643468259/50000000000000000000)
  centralHi := (323899559565286936519/100000000000000000000)
  directionLo := (32773282387608249647/10000000000000000000)
  directionHi := (327732823876082496471/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree044.table
  base := (-3580764500368705617413338988696161365337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-899686857617952774057721657578699573000000000000)
      constant := (9971733896445029113369835016186649677038877067934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree044.table
  base := (-1432553341526978478637920916672854829511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-69340277967515663950163161779654600000000000)
      constant := (770384761180333533798438672529028083113717801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32773282387608249647/10000000000000000000)
  centralHi := (327732823876082496471/100000000000000000000)
  directionLo := (66304353704714069347/20000000000000000000)
  directionHi := (20720110532723146671/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree045.table
  base := (-3545572480470475007106260548254841985033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-102235333112096818831649766938229002000000000000)
      constant := (1160088410651266773685503724109666755563093673934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree045.table
  base := (-354610780914624296243561250571864521143/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-70914940919789276606847138284218600000000000)
      constant := (806619537069210746258069745758069357180775652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66304353704714069347/20000000000000000000)
  centralHi := (20720110532723146671/6250000000000000000)
  directionLo := (67053579222648572161/20000000000000000000)
  directionHi := (167633948056621430403/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree046.table
  base := (-6996815834205333908178779636280305007869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-940549138399789964911974147309422463000000000000)
      constant := (10921007038401834026386071940023427375090117743179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree046.table
  base := (-874717691354427222104040050167139450477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-362448019360314446317655573943913000000000000)
      constant := (4218576681181831514630418890441352540559116056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67053579222648572161/20000000000000000000)
  centralHi := (167633948056621430403/50000000000000000000)
  directionLo := (338972626215458077103/100000000000000000000)
  directionHi := (21185789138466129819/6250000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree047.table
  base := (-6878787363050248579601092935513011074927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-960980278790708560339100392174783908000000000000)
      constant := (11412361143045028414160888927500084629406364687657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree047.table
  base := (-107493552305601006658719449765644248877/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-370321334121682509601075456466733000000000000)
      constant := (4408358216458555735367007448473332930474490048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338972626215458077103/100000000000000000000)
  centralHi := (21185789138466129819/6250000000000000000)
  directionLo := (42829662706362366041/12500000000000000000)
  directionHi := (342637301650898928329/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree048.table
  base := (-1684316860144560289096806954079879928807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-109045713242403017307358515226682817000000000000)
      constant := (1323872474798537933680397045617524492233591236772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree048.table
  base := (-1684489618014011936972483401027698061317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-378194648883050572884495338989553000000000000)
      constant := (4602440112049493171827798753385492605069951788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42829662706362366041/12500000000000000000)
  centralHi := (342637301650898928329/100000000000000000000)
  directionLo := (346263194177223454043/100000000000000000000)
  directionHi := (86565798544305863511/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree049.table
  base := (-6572431939880690638187109783151555973453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1001842559572545751193352881905506798000000000000)
      constant := (12428475575783606623335374347977164336229534156923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree049.table
  base := (-1643257149499804670787820367281962511709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-386067963644418636167915221512373000000000000)
      constant := (4800820525238487644578415772655439638853116876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346263194177223454043/100000000000000000000)
  centralHi := (86565798544305863511/25000000000000000000)
  directionLo := (349851509645189331119/100000000000000000000)
  directionHi := (4373143870564866639/1250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree050.table
  base := (-1596107411408655994670547338319301324647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1022273699963464346620479126770868243000000000000)
      constant := (12953226945269607130943163211051866142495915040708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree050.table
  base := (-6384944604294527130082384162769293301477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-393941278405786699451335104035193000000000000)
      constant := (5003497897787219565749488108324330567364630507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349851509645189331119/100000000000000000000)
  centralHi := (4373143870564866639/1250000000000000000)
  directionLo := (176701696341760152211/50000000000000000000)
  directionHi := (353403392683520304423/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree051.table
  base := (-3086693213082267688151930409118542636753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-400886136237748151498502641920888000000000000)
      constant := (5186121840996987319536707543182816387333374846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree051.table
  base := (-771728836821554238768158455834742568713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-401814593167154762734754986558013000000000000)
      constant := (5210470912019373376486125126965096728708190264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176701696341760152211/50000000000000000000)
  centralHi := (353403392683520304423/100000000000000000000)
  directionLo := (178459965482056298143/50000000000000000000)
  directionHi := (356919930964112596287/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree052.table
  base := (-1484852190736860352714036727984717107293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1063135980745301537474731616501591133000000000000)
      constant := (14036100527023442156054552252721429258115611969452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree052.table
  base := (-5939791897658044721991671645530411737091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-409687907928522826018174869080833000000000000)
      constant := (5421738453684143530431330521838643861881201581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178459965482056298143/50000000000000000000)
  centralHi := (356919930964112596287/100000000000000000000)
  directionLo := (2815641867911193181/781250000000000000)
  directionHi := (360402159092632727169/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree053.table
  base := (-1136517347304663043955069301847817213703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-216713424227244026580371572273390515600000000000)
      constant := (2918843463071442160229543108336231329599724494673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree053.table
  base := (-2841458513834671588380024957268382014963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-417561222689890889301594751603653000000000000)
      constant := (5637299580552552339454536437055948470406515066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815641867911193181/781250000000000000)
  centralHi := (360402159092632727169/100000000000000000000)
  directionLo := (363851062163951638769/100000000000000000000)
  directionHi := (36385106216395163877/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree054.table
  base := (-5402996552531648343130517130779312577931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-122666473503015414258776011803590447000000000000)
      constant := (1684827907846151997009152972539065144856750976069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree054.table
  base := (-5403281187160311821289874854478205000177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-425434537451258952585014634126473000000000000)
      constant := (5857153495861604602716322909917122723153122207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363851062163951638769/100000000000000000000)
  centralHi := (36385106216395163877/10000000000000000000)
  directionLo := (367267579017043442657/100000000000000000000)
  directionHi := (183633789508521721329/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree055.table
  base := (-2550351339350425479368928313203562183829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1124429401918057323756110351097675468000000000000)
      constant := (15743800313874835711856184122418243553159725839078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree055.table
  base := (-1020189576769847601396445328860098892573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-86661570442525403173686903329858600000000000)
      constant := (1216259905171583401941135176160746210848693043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367267579017043442657/100000000000000000000)
  centralHi := (183633789508521721329/50000000000000000000)
  directionLo := (185326302609913346521/50000000000000000000)
  directionHi := (370652605219826693043/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree056.table
  base := (-4775759652708998868317508549517913454287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1144860542308975919183236595963036913000000000000)
      constant := (16335263240222434354693789793687443968481183433417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree056.table
  base := (-4775970820583231289074754890341654497933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-441181166973995079151854399172113000000000000)
      constant := (6309737100807984575151079125042133387431428803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185326302609913346521/50000000000000000000)
  centralHi := (370652605219826693043/100000000000000000000)
  directionLo := (74801399162167854987/20000000000000000000)
  directionHi := (46750874476354909367/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree057.table
  base := (-885642722321245382889888182650142349167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-25895370726664322546896952018408852400000000000)
      constant := (376396415034488605495507301024109266332311628833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree057.table
  base := (-4428395408981673531631504261960067879363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-449054481735363142435274281694933000000000000)
      constant := (6542465738939937276856677192735106639867837933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74801399162167854987/20000000000000000000)
  centralHi := (46750874476354909367/12500000000000000000)
  directionLo := (377331567821529604927/100000000000000000000)
  directionHi := (5895805747211400077/1562500000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree058.table
  base := (-2029051792841057535350077511875650677339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1185722823090813110037489085693759803000000000000)
      constant := (17551525545861332447271486580470364135657303075898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree058.table
  base := (-1014565012353623528673898777147946833487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-456927796496731205718694164217753000000000000)
      constant := (6779485032864250534029592620095483728174145668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377331567821529604927/100000000000000000000)
  centralHi := (5895805747211400077/1562500000000000000)
  directionLo := (380627102600245802643/100000000000000000000)
  directionHi := (95156775650061450661/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree059.table
  base := (-3665462593056825547670439819953629346331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1206153963481731705464615330559121248000000000000)
      constant := (18176322937048165035493985831455741634859678269021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree059.table
  base := (-1832798606693189706668468421899796300113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-464801111258099269002114046740573000000000000)
      constant := (7020794638090731128916708738154777122104202366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380627102600245802643/100000000000000000000)
  centralHi := (95156775650061450661/25000000000000000000)
  directionLo := (383894347956651341617/100000000000000000000)
  directionHi := (191947173978325670809/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree060.table
  base := (-1625159282843674337390197609077949918683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-136287233763627811210193508380498077000000000000)
      constant := (2090247786595312492578043899685535287942736006634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree060.table
  base := (-3250434358829730053694056560250422359717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-472674426019467332285533929263393000000000000)
      constant := (7266394263318174223275321912986883269185762347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383894347956651341617/100000000000000000000)
  centralHi := (191947173978325670809/50000000000000000000)
  directionLo := (387134020143240502527/100000000000000000000)
  directionHi := (1512242266184533213/390625000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree061.table
  base := (-2812695132753343341917334149863698447943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1247016244263568896318867820289844138000000000000)
      constant := (19459246320766478470372233855594810492379174826513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree061.table
  base := (-2812794704100457585909805390551633657559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-480547740780835395568953811786213000000000000)
      constant := (7516283662223041951469966636925970718526956569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387134020143240502527/100000000000000000000)
  centralHi := (1512242266184533213/390625000000000000)
  directionLo := (390346805688827678171/100000000000000000000)
  directionHi := (97586701422206919543/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree062.table
  base := (-18379783463970178862124098535067881759/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1267447384654487491745994065155205583000000000000)
      constant := (20117371109693836940713744290334490913056795925632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree062.table
  base := (-1176348941244436429969431559488145426933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-488421055542203458852373694309033000000000000)
      constant := (7770462626515757405693473712140686530331335606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390346805688827678171/100000000000000000000)
  centralHi := (97586701422206919543/25000000000000000000)
  directionLo := (98383340774326422947/25000000000000000000)
  directionHi := (393533363097305691789/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree063.table
  base := (-233760865917227423130832663939596968793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-143097613893934009685902256668951892000000000000)
      constant := (2309622664392467317284878614949127605657669545656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree063.table
  base := (-935080247845376782901543203899454417693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-496294370303571522135793576831853000000000000)
      constant := (8028930980068930080432401261300960376165389926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98383340774326422947/25000000000000000000)
  centralHi := (393533363097305691789/100000000000000000000)
  directionLo := (396694324423579685677/100000000000000000000)
  directionHi := (198347162211789842839/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree064.table
  base := (-85320835579256599435748028441717590657/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1308309665436324682600246554885928473000000000000)
      constant := (21466944535558506931402330021166195133247238817392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree064.table
  base := (-170649572729537683792851774774906223031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-504167685064939585419213459354673000000000000)
      constant := (8291688573952036665142340128579816159038912968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396694324423579685677/100000000000000000000)
  centralHi := (198347162211789842839/50000000000000000000)
  directionLo := (99957574184339808891/25000000000000000000)
  directionHi := (79966059347471847113/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree065.table
  base := (-837763710020021136250514388403225435237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1328740805827243278027372799751289918000000000000)
      constant := (22158392443862025268912153119023084649836041304867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree065.table
  base := (-837818011266871704814394437069727653873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-512040999826307648702633341877493000000000000)
      constant := (8558735282232625723235791718608672259320061343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99957574184339808891/25000000000000000000)
  centralHi := (79966059347471847113/20000000000000000000)
  directionLo := (402941863484410351761/100000000000000000000)
  directionHi := (201470931742205175881/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree066.table
  base := (-57597637212790176936370405789674782177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-29981598804848041632322200991481141400000000000)
      constant := (508021053821722331998405070904742950728170535823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree066.table
  base := (-72008705303306070111598323685435322821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-519914314587675711986053224400313000000000000)
      constant := (8830070998425716121753632172886482866640768044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402941863484410351761/100000000000000000000)
  centralHi := (201470931742205175881/50000000000000000000)
  directionLo := (406029585753912318863/100000000000000000000)
  directionHi := (25376849109619519929/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree067.table
  base := (284184543328669919737452559411670857143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1369603086609080468881625289482012808000000000000)
      constant := (23574609230960932026884796796301291166962041656287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree067.table
  base := (284144501192766587858980756553807939909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-527787629349043775269473106923133000000000000)
      constant := (9105695632491325807149963961731350348434494581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406029585753912318863/100000000000000000000)
  centralHi := (25376849109619519929/6250000000000000000)
  directionLo := (409094003459715951053/100000000000000000000)
  directionHi := (204547001729857975527/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree068.table
  base := (219686788285995976927052703963501509319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (68854365884794289280473878289190000000000000)
      linear := (-4809807013840827212141008769368077000000000000)
      constant := (84080891587148125343974743262791057350445149756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree068.table
  base := (878712779597027776137762128236904321601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-535660944110411838552892989445953000000000000)
      constant := (9385609108295514417652653374214029317947865009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409094003459715951053/100000000000000000000)
  centralHi := (204547001729857975527/50000000000000000000)
  directionLo := (20606781822127305159/5000000000000000000)
  directionHi := (412135636442546103181/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree069.table
  base := (373923361775607910344895497655892082833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-156718374154546406637319753245859522000000000000)
      constant := (2781694729352437733650649907815899782252432243332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree069.table
  base := (1495663946048161871526229835375383453829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-543534258871779901836312871968773000000000000)
      constant := (9669811361463385578108629194405374443061671861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20606781822127305159/5000000000000000000)
  centralHi := (412135636442546103181/100000000000000000000)
  directionLo := (207577492749760194609/50000000000000000000)
  directionHi := (415154985499520389219/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree070.table
  base := (1067509091895278089876612526466249203489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1430896507781836255163004024078097143000000000000)
      constant := (25782233772787716058675221207102109097434636594802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree070.table
  base := (2134992869864799356170129049426775911683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-551407573633147965119732754491593000000000000)
      constant := (9958302337563540639302975632829378665647044947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207577492749760194609/50000000000000000000)
  centralHi := (415154985499520389219/100000000000000000000)
  directionLo := (209076266673378923767/50000000000000000000)
  directionHi := (83630506669351569507/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree071.table
  base := (2796716929572472226197099156021668705479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1451327648172754850590130268943458588000000000000)
      constant := (26540321172191349070268584708409809759079005875311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree071.table
  base := (2796695212922402213645829701996241991757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-559280888394516028403152637014413000000000000)
      constant := (10251081990572816377419454398090441131290550013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209076266673378923767/50000000000000000000)
  centralHi := (83630506669351569507/20000000000000000000)
  directionLo := (210564372760158480437/50000000000000000000)
  directionHi := (3369029964162535687/800000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree072.table
  base := (696157186831293362854086222938118619413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-32705750856970521022605700306862667400000000000)
      constant := (606878103531050119053656806245040425425238877413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree072.table
  base := (1740383653640516024045186543719965927537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-567154203155884091686572519537233000000000000)
      constant := (10548150281578037986016355361280386237050480066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210564372760158480437/50000000000000000000)
  centralHi := (3369029964162535687/800000000000000000)
  directionLo := (212042035610112182653/50000000000000000000)
  directionHi := (424084071220224365307/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree073.table
  base := (837444405065487703849536121995114878619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-298437985790918408288876551734836295600000000000)
      constant := (5617962829074260572292669308572358024341646593571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree073.table
  base := (52340075646315000448790600164744415341/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-115005503583450430993998480412010600000000000)
      constant := (2169901435535639632832820139831430176037642704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212042035610112182653/50000000000000000000)
  centralHi := (424084071220224365307/100000000000000000000)
  directionLo := (427018944101927146393/100000000000000000000)
  directionHi := (213509472050963573197/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree074.table
  base := (4916022519893286476057406778241368069937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1512621069345510636871509003539542923000000000000)
      constant := (28881219557573464602415266369080603981694154207433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree074.table
  base := (2458004412079663881940071382229495727913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-582900832678620218253412284582873000000000000)
      constant := (11155152651056121460477005868738887440354858034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427018944101927146393/100000000000000000000)
  centralHi := (213509472050963573197/50000000000000000000)
  directionLo := (214966891509558530609/50000000000000000000)
  directionHi := (429933783019117061219/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree075.table
  base := (1416796287086999255260048714868392866401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-170339134415158803588737249822767152000000000000)
      constant := (3298192314764330134853463877317854495212113329604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree075.table
  base := (141679335195314271321705529756757128661/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-118154829487997656307366433421138600000000000)
      constant := (2293017335638689889387327686259910491023716392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214966891509558530609/50000000000000000000)
  centralHi := (429933783019117061219/100000000000000000000)
  directionLo := (216414496360764658777/50000000000000000000)
  directionHi := (86565798544305863511/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree076.table
  base := (3220353995569395939392241342457342206187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1553483350127347827725761493270265813000000000000)
      constant := (30497347918319666055554360998013295568907207867366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree076.table
  base := (6440697928467478730924994399570606255563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-598647462201356344820252049628513000000000000)
      constant := (11779309239206821370425260522194072561765267867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216414496360764658777/50000000000000000000)
  centralHi := (86565798544305863511/20000000000000000000)
  directionLo := (108926241127751824209/25000000000000000000)
  directionHi := (435704964511007296837/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree077.table
  base := (3618294712375040780905213139523456598239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1573914490518266423152887738135627258000000000000)
      constant := (31322070769096245340077000473559385538290832700302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree077.table
  base := (904572600206114118520473038862384324371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-606520776962724408103671932151333000000000000)
      constant := (12097820317286540487128024373656229282378015512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108926241127751824209/25000000000000000000)
  centralHi := (435704964511007296837/100000000000000000000)
  directionLo := (219281038429421991517/50000000000000000000)
  directionHi := (87712415371768796607/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree078.table
  base := (2013707019023058557799478364882317313137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-177149514545465002064445998111220967000000000000)
      constant := (3573099927479962378719916132962048165057581420548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree078.table
  base := (4027410343930947868800168635206664280581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-614394091724092471387091814674153000000000000)
      constant := (12420619898221904577914994038672409002705367658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219281038429421991517/50000000000000000000)
  centralHi := (87712415371768796607/20000000000000000000)
  directionLo := (220700347993578742629/50000000000000000000)
  directionHi := (441400695987157485259/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree079.table
  base := (4447711391958020891821369315804482782057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1614776771300103614007140227866350148000000000000)
      constant := (33004833620946393161115645988390980652881851793026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree079.table
  base := (8895416454757282289680377706397885301873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-622267406485460534670511697196973000000000000)
      constant := (12747707969999821565501608207702282165167570657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220700347993578742629/50000000000000000000)
  centralHi := (441400695987157485259/100000000000000000000)
  directionLo := (3470477940756476227/781250000000000000)
  directionHi := (444221176416828957057/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree080.table
  base := (609898285385673175061865438413771923163/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1635207911691022209434266472731711593000000000000)
      constant := (33862873562877723821589031503743846030747314087472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree080.table
  base := (9758367145138832239067820683312649864437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-630140721246828597953931579719793000000000000)
      constant := (13079084522465396535852016355664703902411812133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3470477940756476227/781250000000000000)
  centralHi := (444221176416828957057/100000000000000000000)
  directionLo := (223511930742161907203/50000000000000000000)
  directionHi := (447023861484323814407/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree081.table
  base := (1330459574048793752940196726995984835343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-183959894675771200540154746399674782000000000000)
      constant := (3859113238910862793929345684774573887134171786744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree081.table
  base := (425746877996395378137728743557375516689/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-25520561440327866449494058489704520000000000)
      constant := (536589981881396920440537658513663916856553601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223511930742161907203/50000000000000000000)
  centralHi := (447023861484323814407/100000000000000000000)
  directionLo := (44980908382952914001/10000000000000000000)
  directionHi := (449809083829529140011/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree082.table
  base := (180489596255206894565538974895995002597/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1676070192472859400288518962462434483000000000000)
      constant := (35612270363528857807202636915102272391599465047872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree082.table
  base := (5775665092598526869625386874342915554247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-645887350769564724520771344765433000000000000)
      constant := (13754703036453188247467450071703373982230012846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44980908382952914001/10000000000000000000)
  centralHi := (449809083829529140011/100000000000000000000)
  directionLo := (45257716585656950521/10000000000000000000)
  directionHi := (452577165856569505211/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree083.table
  base := (12481344676220820398401676334824582937951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1696501332863777995715645207327795928000000000000)
      constant := (36503627186486269109995972269700168529636066335559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree083.table
  base := (6240670636503045865868832177916959872109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-653760665530932787804191227288253000000000000)
      constant := (14098944984588251264312379495702401054566408762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45257716585656950521/10000000000000000000)
  centralHi := (452577165856569505211/100000000000000000000)
  directionLo := (113832105042352087133/25000000000000000000)
  directionHi := (455328420169408348533/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree084.table
  base := (13433707638020004265140410352256153925087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-190770274806077399015863494688128597000000000000)
      constant := (4156232178357432626412030632627015153190470667087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree084.table
  base := (13433704724864604585372264971023194109873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-661633980292300851087611109811073000000000000)
      constant := (14447475386257908435240984720552557066311642657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113832105042352087133/25000000000000000000)
  centralHi := (455328420169408348533/100000000000000000000)
  directionLo := (114515787495975233007/25000000000000000000)
  directionHi := (458063149983900932029/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree085.table
  base := (144084226213012259482624772425804751559/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38192400000000000000000000000000000000000000
      center := (572886)
      previous := (286443)
      next := (286443)
      square := (2754174635391771571218955131567600000000000)
      linear := (-240465552061676842431819750457926480000000000)
      constant := (5303758838478756830632578420610106978934419516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree085.table
  base := (14408420127990502560822305076882775377253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-669507295053668914371030992333893000000000000)
      constant := (14800294237082954570208689688335054363977277077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114515787495975233007/25000000000000000000)
  centralHi := (458063149983900932029/100000000000000000000)
  directionLo := (230390824758918171571/50000000000000000000)
  directionHi := (460781649517836343143/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree086.table
  base := (481421539602346284833138635328703841577/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1757794754036533781997023941923880263000000000000)
      constant := (39244331184962204448559876739534212704409929990176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree086.table
  base := (15405487133596243575028713425753172890713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-677380609815036977654450874856713000000000000)
      constant := (15157401533363102635256320712183473411197574217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230390824758918171571/50000000000000000000)
  centralHi := (460781649517836343143/100000000000000000000)
  directionLo := (463484204360388767857/100000000000000000000)
  directionHi := (231742102180194383929/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree087.table
  base := (16424907272672063819208866536516886761917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-197580654936383597491572242976582412000000000000)
      constant := (4464456703078670133661269363347079910953924283917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree087.table
  base := (4106226361749782594551382627136625729989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-685253924576405040937870757379533000000000000)
      constant := (15518797271972063895260898547665900849477813204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463484204360388767857/100000000000000000000)
  centralHi := (231742102180194383929/50000000000000000000)
  directionLo := (93234218364458243059/20000000000000000000)
  directionHi := (7283923309723300239/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree088.table
  base := (8733338190590748531956120572171423798533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1798657034818370972851276431654603153000000000000)
      constant := (41126995029173859236616240134509076309679067577594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree088.table
  base := (17466674819258825693969111943697400238923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-693127239337773104221290639902353000000000000)
      constant := (15884481450268830312057269111538309719134734107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93234218364458243059/20000000000000000000)
  centralHi := (7283923309723300239/1562500000000000000)
  directionLo := (23442129063397351571/5000000000000000000)
  directionHi := (468842581267947031421/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree089.table
  base := (18530796376209489239945514819983949809227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1819088175209289568278402676519964598000000000000)
      constant := (42084985283382994755155381552318136331016358121043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree089.table
  base := (18530795040106295972462875281798070978559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-701000554099141167504710522425173000000000000)
      constant := (16254454066022657708715003920594932735011532431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23442129063397351571/5000000000000000000)
  centralHi := (468842581267947031421/100000000000000000000)
  directionLo := (7367170850478203333/1562500000000000000)
  directionHi := (471498934430605013313/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree090.table
  base := (19617267074752738979067035387143764105271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-204391035066689795967280991265036227000000000000)
      constant := (4783786787253960334842652895469256222890524991271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree090.table
  base := (19617265931964795472315738071704993411279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-708873868860509230788130404947993000000000000)
      constant := (16628715117349634389663897161111588275100258911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7367170850478203333/1562500000000000000)
  centralHi := (471498934430605013313/100000000000000000000)
  directionLo := (118535101427910483403/25000000000000000000)
  directionHi := (474140405711641933613/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree091.table
  base := (20726088322216304998884262443351506405723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1859950455991126759132655166250687488000000000000)
      constant := (44034282430615909810800912353825942896548078113507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree091.table
  base := (10363043672447142023726210006656075149003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-716747183621877294071550287470813000000000000)
      constant := (17007264602659046468994236184384451602511545654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118535101427910483403/25000000000000000000)
  centralHi := (474140405711641933613/100000000000000000000)
  directionLo := (476767242464921098311/100000000000000000000)
  directionHi := (59595905308115137289/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree092.table
  base := (273215749850374146665319365973289717967/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-376076319276409070911956282223209786600000000000)
      constant := (9005117863154167667916249984248991337995021755248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree092.table
  base := (21857259152316701750724934470889391835703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-724620498383245357354970169993633000000000000)
      constant := (17390102520608027308726728000195061557984973127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476767242464921098311/100000000000000000000)
  centralHi := (59595905308115137289/12500000000000000000)
  directionLo := (239689842633563277601/50000000000000000000)
  directionHi := (479379685267126555203/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree093.table
  base := (11505390980969959113543277898605053034579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-211201415196995994442989739553490042000000000000)
      constant := (5114222415300898553721021156211345781543144497158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree093.table
  base := (2301078124740153474542415376377927386807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-146498762628922684127678010503290600000000000)
      constant := (3555445774012642397513545094595864663293270926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239689842633563277601/50000000000000000000)
  centralHi := (479379685267126555203/100000000000000000000)
  directionLo := (481977968174909175381/100000000000000000000)
  directionHi := (240988984087454587691/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree094.table
  base := (48373308301744929896075140156276241111/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11037603600000000000000000000000000000000000000
      center := (165564054)
      previous := (82782027)
      next := (82782027)
      square := (795956469628221984082278033023036400000000000)
      linear := (-76849755086555301816561356033870872920000000000)
      constant := (1881660787754375059222506901804789040154062079980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree094.table
  base := (24186653540009720363525384673380374088821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-740367127905981483921809935039273000000000000)
      constant := (18168643650068315189672154632381094388708301989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481977968174909175381/100000000000000000000)
  centralHi := (240988984087454587691/50000000000000000000)
  directionLo := (242281159484811267357/50000000000000000000)
  directionHi := (96912463793924506943/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree095.table
  base := (6346219119070115525951658499252849186941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1941675017554801140841160145712133268000000000000)
      constant := (48066143182057277176269755795986568555585370545876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree095.table
  base := (25384875954109679030988367373617327533313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-748240442667349547205229817562093000000000000)
      constant := (18564346859816717887339022361905541227800917617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242281159484811267357/50000000000000000000)
  centralHi := (96912463793924506943/20000000000000000000)
  directionLo := (243566479695186433101/50000000000000000000)
  directionHi := (487132959390372866203/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree096.table
  base := (5321089774379848643018719500640316262767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-43602359065460438583739697568388771400000000000)
      constant := (1091152715566072917053302966762316676701959884767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree096.table
  base := (5321089685118514156512465308107388943011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-151222751485743522097729940016982600000000000)
      constant := (3792867699725657879475396637228168889296403699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243566479695186433101/50000000000000000000)
  centralHi := (487132959390372866203/100000000000000000000)
  directionLo := (244845052678028961771/50000000000000000000)
  directionHi := (489690105356057923543/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree097.table
  base := (54391350159859959583418561823934633869/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-1982537298336638331695412635442856158000000000000)
      constant := (50148706747565421486363382890698242019750160100352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree097.table
  base := (27848370900425129320991099022075956305623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-763987072190085673772069582607733000000000000)
      constant := (19368618565929790797638446470206764820446354407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244845052678028961771/50000000000000000000)
  centralHi := (489690105356057923543/100000000000000000000)
  directionLo := (492233967177024017807/100000000000000000000)
  directionHi := (30764622948564001113/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree098.table
  base := (29113643659025653820449159399242509898407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2002968438727556927122538880308217603000000000000)
      constant := (51206646822033965468099034608686018540319231843663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree098.table
  base := (7278410833271986060372052563295774416613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-771860386951453737055489465130553000000000000)
      constant := (19777187061238306663139032505442673483143389268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492233967177024017807/100000000000000000000)
  centralHi := (30764622948564001113/6250000000000000000)
  directionLo := (494764749756928426191/100000000000000000000)
  directionHi := (30922796859808026637/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree099.table
  base := (6080253192749961669782698002659254991211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-44964435091521678278881447226079534400000000000)
      constant := (1161682053839643146409297758873474509187307917211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree099.table
  base := (7600316421313777594428380493433029054739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-779733701712821800338909347653373000000000000)
      constant := (20190043984147237465969038765046891020966904204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494764749756928426191/100000000000000000000)
  centralHi := (30922796859808026637/6250000000000000000)
  directionLo := (497282652785355520103/100000000000000000000)
  directionHi := (62160331598169440013/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree100.table
  base := (15855619081305557379030711334945262202613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2043830719509394117976791370038940493000000000000)
      constant := (53355843548893443716023891867418288084452525891034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree100.table
  base := (31711237924677969057874249066021014975591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-787607016474189863622329230176193000000000000)
      constant := (20607189334314457186279415591705716947876044919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497282652785355520103/100000000000000000000)
  centralHi := (62160331598169440013/12500000000000000000)
  directionLo := (62473483865212380557/12500000000000000000)
  directionHi := (499787870921699044457/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree101.table
  base := (33043560227500304967550679609305986906519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2064261859900312713403917614904301938000000000000)
      constant := (54447100199586824454523135227439630642577367444671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree101.table
  base := (33043560024241421200660606875682776778577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-795480331235557926905749112699013000000000000)
      constant := (21028623111452301737916547480020971578843923393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62473483865212380557/12500000000000000000)
  centralHi := (499787870921699044457/100000000000000000000)
  directionLo := (251140296985394875877/50000000000000000000)
  directionHi := (100456118794157950351/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree102.table
  base := (8599558033696720089028736595470859286589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-801496732138112767716664305947583000000000000)
      constant := (21356963619458678820563790448692677384685690804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree102.table
  base := (3439823196116615883166566111475463750159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-160670729199385198037833799044366600000000000)
      constant := (4290869063063821088515990252826331589850873662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251140296985394875877/50000000000000000000)
  centralHi := (100456118794157950351/20000000000000000000)
  directionLo := (20190440282028673121/4000000000000000000)
  directionHi := (252380503525358414013/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree103.table
  base := (3577525386462426784184576764496882194407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (78030)
      previous := (39015)
      next := (39015)
      square := (375132656060053720464830819598000000000000)
      linear := (-39685628064514090003924405780658400000000000)
      constant := (1068204921712157501613203947635914106175305214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree103.table
  base := (3577525371633427692339435713390401128731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (144226319131124075534344798000000000000)
      linear := (-15293184291795533103451576543400000000000)
      constant := (412562087769102581691637890644980802257462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20190440282028673121/4000000000000000000)
  centralHi := (252380503525358414013/50000000000000000000)
  directionLo := (126807322688315759491/25000000000000000000)
  directionHi := (101445858150652607593/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree104.table
  base := (37174625400362207074114200102968503896477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2125555281073068499685296349500386273000000000000)
      constant := (57787503293155490202913490346372759805235921406293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree104.table
  base := (7434925054743841488699913655680050630529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-163820055103932423351201752053494600000000000)
      constant := (4463731000492219777484063749746996057139282161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126807322688315759491/25000000000000000000)
  centralHi := (101445858150652607593/20000000000000000000)
  directionLo := (254842810648673539091/50000000000000000000)
  directionHi := (509685621297347078183/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree105.table
  base := (38596346728049842623071589954948477750693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-238442935718220788345824732707305302000000000000)
      constant := (6547020226292150019057859685278431650857102488693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree105.table
  base := (38596346619903860218636461123222262620041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-826973590281030180039428642790293000000000000)
      constant := (22757242485423920857693096444741529984136014969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254842810648673539091/50000000000000000000)
  centralHi := (509685621297347078183/100000000000000000000)
  directionLo := (256065085337921045579/50000000000000000000)
  directionHi := (512130170675842091159/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree106.table
  base := (20020208918007770478957633792817277026893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2166417561854905690539548839231109163000000000000)
      constant := (60069966302320907418200473223158536398271157368074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree106.table
  base := (40040417743673343626121252416222084984343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-834846905042398243322848525313113000000000000)
      constant := (23200118394481533571426212740760618099598894887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256065085337921045579/50000000000000000000)
  centralHi := (512130170675842091159/100000000000000000000)
  directionLo := (257281553398058252427/50000000000000000000)
  directionHi := (102912621359223300971/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree107.table
  base := (8301367742902321152402492810445563294099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-437369740449164857193335016819294121600000000000)
      constant := (12245571217992236784612453407485640128872437452891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree107.table
  base := (41506838635670742349313064280704010979863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-842720219803766306606268407835933000000000000)
      constant := (23647282729534669514025424563398379852485366567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257281553398058252427/50000000000000000000)
  centralHi := (102912621359223300971/20000000000000000000)
  directionLo := (516984593614622183973/100000000000000000000)
  directionHi := (258492296807311091987/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree108.table
  base := (42995609355413887140991399165841041788513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-245253315848526986821533480995759117000000000000)
      constant := (6932983488814000202311497184270744650964622646513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree108.table
  base := (42995609288106208784853021349085891812971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-850593534565134369889688290358753000000000000)
      constant := (24098735490500686192266697603880136226243809339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516984593614622183973/100000000000000000000)
  centralHi := (258492296807311091987/50000000000000000000)
  directionLo := (103878958253167036213/20000000000000000000)
  directionHi := (259697395632917590533/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree109.table
  base := (22253364875983910817943755659086102334727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2227710983027661476820927573827193498000000000000)
      constant := (63576952230228975626546356842483499479323755701086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree109.table
  base := (5563341211813891165528973367207360236003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-858466849326502433173108172881573000000000000)
      constant := (24554476677310958084377356309328420077950046616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103878958253167036213/20000000000000000000)
  centralHi := (259697395632917590533/50000000000000000000)
  directionLo := (130448464046459010699/25000000000000000000)
  directionHi := (521793856185836042797/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree110.table
  base := (46040199898573743884384572245064015571051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2248142123418580072248053818692554943000000000000)
      constant := (64768158582515588123886171326001382881243721433459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree110.table
  base := (287751249059564994123568847056557898849/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-173268032817574099291305611080878600000000000)
      constant := (5002901257981734576478368222429882727964449312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130448464046459010699/25000000000000000000)
  centralHi := (521793856185836042797/100000000000000000000)
  directionLo := (524181941230799552423/100000000000000000000)
  directionHi := (65522742653849944053/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree111.table
  base := (23798009895302706924180052273570973778483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-252063695978833185297242229284212932000000000000)
      constant := (7330052272895353644841645124947746085976605312966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree111.table
  base := (47596019748746914349898191422791560501241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-874213478849238559739947937927213000000000000)
      constant := (25478824328246969533776709193276878665357665769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524181941230799552423/100000000000000000000)
  centralHi := (65522742653849944053/12500000000000000000)
  directionLo := (526559195790647876943/100000000000000000000)
  directionHi := (32909949736915492309/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree112.table
  base := (49174189424256636682216470421321004077083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2289004404200417263102306308423277833000000000000)
      constant := (67183887850751731490787086410151427534392064995747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree112.table
  base := (49174189388533302447937978748395549123159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-882086793610606623023367820450033000000000000)
      constant := (25947430792287365241062481914460784380647593831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526559195790647876943/100000000000000000000)
  centralHi := (32909949736915492309/6250000000000000000)
  directionLo := (52892576589810624757/10000000000000000000)
  directionHi := (528925765898106247571/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree113.table
  base := (50774708796411641725853180864983605880931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2309435544591335858529432553288639278000000000000)
      constant := (68408410766510257581886263348423890657655862942379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree113.table
  base := (10154941753185335339613596215391873892827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-177992021674394937261357540594570600000000000)
      constant := (5284065136399685347943507894397382190129001643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52892576589810624757/10000000000000000000)
  centralHi := (528925765898106247571/100000000000000000000)
  directionLo := (132820448583346613521/25000000000000000000)
  directionHi := (106256358866677290817/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree114.table
  base := (13099394476133888727399803601419259555643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-258874076109139383772950977572666747000000000000)
      constant := (7738226578140423748775552016199672297867443974572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree114.table
  base := (10479515575704571263607635476969800495111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-179566684626668549918041517099134600000000000)
      constant := (5379501799470929615164598278563105013452632599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132820448583346613521/25000000000000000000)
  centralHi := (106256358866677290817/20000000000000000000)
  directionLo := (533627420724710502583/100000000000000000000)
  directionHi := (66703427590588812823/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree115.table
  base := (27021398373290931893397599230039388407781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2350297825373173049383685043019362168000000000000)
      constant := (70890773160955928479196470055272352618782609168058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree115.table
  base := (27021398362193519929635740110735838965629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-905706737894710812873627468018493000000000000)
      constant := (27378980738335502940810883356183288031172716122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533627420724710502583/100000000000000000000)
  centralHi := (66703427590588812823/12500000000000000000)
  directionLo := (535962781644874704129/100000000000000000000)
  directionHi := (53596278164487470413/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree116.table
  base := (55710365320914252308869040706963131607643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2370728965764091644810811287884723613000000000000)
      constant := (72148612639541449282764626324189063889249485410787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree116.table
  base := (5571036530197838656851285735843403502081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-182716010531215775231409470108262600000000000)
      constant := (5572948180984928911025986545035834935507154658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535962781644874704129/100000000000000000000)
  centralHi := (53596278164487470413/10000000000000000000)
  directionLo := (134572002676010791513/25000000000000000000)
  directionHi := (538288010704043166053/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree117.table
  base := (57400283626240586732948654806561882744439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-265684456239445582248659725861120562000000000000)
      constant := (8157506404331635666617157879582093686181332718439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree117.table
  base := (11480056722017270636942600272023610096099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-184290673483489387888093446612826600000000000)
      constant := (5670957899421846053064733479443742679509514291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134572002676010791513/25000000000000000000)
  centralHi := (538288010704043166053/100000000000000000000)
  directionLo := (540603238638949090753/100000000000000000000)
  directionHi := (270301619319474545377/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree118.table
  base := (59112551661557176043851793624007304478539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2411591246545928835665063777615446503000000000000)
      constant := (74697608159258047770659695767341926239846545472851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree118.table
  base := (29556275823888483139652953653732363565021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-929326682178815002723887115586953000000000000)
      constant := (28849126514879351547288430626115607290122615578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540603238638949090753/100000000000000000000)
  centralHi := (270301619319474545377/50000000000000000000)
  directionLo := (271454296699336197953/50000000000000000000)
  directionHi := (542908593398672395907/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree119.table
  base := (1216943388522034391490518189822453815579/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38192400000000000000000000000000000000000000
      center := (572886)
      previous := (286443)
      next := (286443)
      square := (2754174635391771571218955131567600000000000)
      linear := (-336612095077764350324178549824333280000000000)
      constant := (10517476013887943898216345588051171770530596998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree119.table
  base := (60847169414347491464529345210092312265349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-937199996940183066007306998109773000000000000)
      constant := (29347751958227553091904452913901896340823087541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271454296699336197953/50000000000000000000)
  centralHi := (542908593398672395907/100000000000000000000)
  directionLo := (136301050056788226599/25000000000000000000)
  directionHi := (545204200227152906397/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree120.table
  base := (782551711491419990472960894894322710207/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-54498967273950356144873694829914875400000000000)
      constant := (1717578350271473155130504049894851911181077955312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree120.table
  base := (12520827381857639716471898103632933120293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-189014662340310225858145376126518600000000000)
      constant := (5970133165429685434385051901185673787473188437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136301050056788226599/25000000000000000000)
  centralHi := (545204200227152906397/100000000000000000000)
  directionLo := (6843627271782371093/1250000000000000000)
  directionHi := (547490181742589687441/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree121.table
  base := (64383454140800380804088551788311466517569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2472884667718684621946442512211530838000000000000)
      constant := (78604392844874910885772308855061214718013997644121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree121.table
  base := (64383454132250123051239313907164500236271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-952946626462919192574146763155413000000000000)
      constant := (30357868121638271622105111878091221183006599039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6843627271782371093/1250000000000000000)
  centralHi := (547490181742589687441/100000000000000000000)
  directionLo := (549766658013868948901/100000000000000000000)
  directionHi := (274883329006934474451/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree122.table
  base := (16546280272577390945326646447411821612669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2493315808109603217373568757076892283000000000000)
      constant := (79928865448309283878463931667011907240145531600084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree122.table
  base := (13237024216603578711829507396260393140899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-192163988244857451171513329135646600000000000)
      constant := (6173871768338960313638955257577903710831797491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549766658013868948901/100000000000000000000)
  centralHi := (274883329006934474451/50000000000000000000)
  directionLo := (552033746634155314869/100000000000000000000)
  directionHi := (55203374663415531487/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree123.table
  base := (1700228444192619189824522436091253568327/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-55861043300011595840015444487605638400000000000)
      constant := (1805876523833681059379820143359869180578953202616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree123.table
  base := (68009137761486840044381561036216607296513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-968693255985655319140986528201053000000000000)
      constant := (31385137987316906565509649865668700986808706417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552033746634155314869/100000000000000000000)
  centralHi := (55203374663415531487/10000000000000000000)
  directionLo := (277145781395887042591/50000000000000000000)
  directionHi := (554291562791774085183/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree124.table
  base := (6985550417294566705760333144785833680339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-506835617778288081645564249361523034600000000000)
      constant := (16522225443498577906646954107323661308695554978102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree124.table
  base := (1397110083352874349083603968920683947951/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-39062662829880935296976256428954920000000000)
      constant := (1276208222340177843891399566876234752007624318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277145781395887042591/50000000000000000000)
  centralHi := (554291562791774085183/100000000000000000000)
  directionLo := (556540219338505384297/100000000000000000000)
  directionHi := (278270109669252692149/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree125.table
  base := (35862110153035548086316185551669602077243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2554609229282359003654947491672976618000000000000)
      constant := (83968916383242081047567899288620489257616724074374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree125.table
  base := (2868968812062019341779952757440002543171/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-39377595420335657828313051729867720000000000)
      constant := (1297182462210323098934148988960645986980501139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556540219338505384297/100000000000000000000)
  centralHi := (278270109669252692149/50000000000000000000)
  directionLo := (69847478356925596001/12500000000000000000)
  directionHi := (558779826855404768009/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree126.table
  base := (73615286167184828867462366282016166448073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-286115596630364177675785970726482007000000000000)
      constant := (9481979007751787305981440640235073890345958266073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree126.table
  base := (36807643081665327940528009209327973223277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-992313200269759508991246175769513000000000000)
      constant := (32958205977579111091570565106035698935851491386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69847478356925596001/12500000000000000000)
  centralHi := (558779826855404768009/100000000000000000000)
  directionLo := (561010493716258912403/100000000000000000000)
  directionHi := (140252623429064728101/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree127.table
  base := (73758497809026973859686757048139476481/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2595471510064196194509199981403699508000000000000)
      constant := (86717811277069229180994468867245728043431530384896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree127.table
  base := (75528701753157846673776349579319530426433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1000186515031127572274666058292333000000000000)
      constant := (33491138825469388803870599897403051898294027697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561010493716258912403/100000000000000000000)
  centralHi := (140252623429064728101/25000000000000000000)
  directionLo := (563232326148779416533/100000000000000000000)
  directionHi := (281616163074389708267/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree128.table
  base := (77464467074047163881831446894827165470791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2615902650455114789936326226269060953000000000000)
      constant := (88108917005157021593669681777728872201445496091119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree128.table
  base := (77464467071246136197032712773015672501101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1008059829792495635558085940815153000000000000)
      constant := (34028360098931181787884651197984667269564180509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563232326148779416533/100000000000000000000)
  centralHi := (281616163074389708267/50000000000000000000)
  directionLo := (22617817131745299483/4000000000000000000)
  directionHi := (141361357073408121769/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree129.table
  base := (39711291060114823687230482998464308023329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-292925976760670376151494719014935822000000000000)
      constant := (9945680917115102805359613256032744384852669474658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree129.table
  base := (19855645529460499517412207589289803396703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1015933144553863698841505823337973000000000000)
      constant := (34569869797967104882234819878270359096942488508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22617817131745299483/4000000000000000000)
  centralHi := (141361357073408121769/25000000000000000000)
  directionLo := (17739059445668666183/3125000000000000000)
  directionHi := (567649902261397317857/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree130.table
  base := (81403046895252689505708683501229764261907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2656764931236951980790578715999783843000000000000)
      constant := (90924445023713159228498593081711931091110940115163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree130.table
  base := (81403046893217534073803993937089875103063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1023806459315231762124925705860793000000000000)
      constant := (35115667922580044814728246042901176484968395367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17739059445668666183/3125000000000000000)
  centralHi := (567649902261397317857/100000000000000000000)
  directionLo := (284922924093770654627/50000000000000000000)
  directionHi := (113969169637508261851/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree131.table
  base := (41702930699699706056503393548647266172923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2677196071627870576217704960865145288000000000000)
      constant := (92348867314196536000986103433976083159827065636614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree131.table
  base := (83405861397664813734263747683780096408979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1031679774076599825408345588383613000000000000)
      constant := (35665754472773100150953167349986966042802858211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284922924093770654627/50000000000000000000)
  centralHi := (113969169637508261851/20000000000000000000)
  directionLo := (8938021316960873023/1562500000000000000)
  directionHi := (572033364285495873473/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree132.table
  base := (21357756408242371965973733552090038331657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-299736356890976574627203467303389637000000000000)
      constant := (10420488347277147192887132630653431187459594774628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree132.table
  base := (3417241025259645824747133930954836800487/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-41582123553518715547670618836257320000000000)
      constant := (1448805177941981245100151414904408503616366583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8938021316960873023/1562500000000000000)
  centralHi := (572033364285495873473/100000000000000000000)
  directionLo := (574212546897912424007/100000000000000000000)
  directionHi := (71776568362239053001/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree133.table
  base := (43739269798137502634445152296879283549553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2718058352409707767071957450595868178000000000000)
      constant := (95231028457615137206660871460359947056484834855954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree133.table
  base := (87478539595015134152324313137670065828077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1047426403599335951975185353429253000000000000)
      constant := (36778792849912717818727858684189050728370068893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574212546897912424007/100000000000000000000)
  centralHi := (71776568362239053001/12500000000000000000)
  directionLo := (288191745273087117619/50000000000000000000)
  directionHi := (576383490546174235239/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree134.table
  base := (44774201644818511823372977019608966963273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2738489492800626362499083695461229623000000000000)
      constant := (96688767310567832726747342477542167193730515662914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree134.table
  base := (89548403288563398424499954615776997139407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1055299718360704015258605235952073000000000000)
      constant := (37341744676866125326543753080344900162651968863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288191745273087117619/50000000000000000000)
  centralHi := (576383490546174235239/100000000000000000000)
  directionLo := (578546287978236165833/100000000000000000000)
  directionHi := (289273143989118082917/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree135.table
  base := (11455077089172838704084487681086516162563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-306546737021282773102912215591843452000000000000)
      constant := (10906401298262382126146689120221046052752474564504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree135.table
  base := (91640616712467848639684843094974742034991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1063173033122072078542025118474893000000000000)
      constant := (37908984929413274886310792323311142038249219519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578546287978236165833/100000000000000000000)
  centralHi := (289273143989118082917/50000000000000000000)
  directionLo := (580701030214860753791/100000000000000000000)
  directionHi := (4536726798553599639/781250000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree136.table
  base := (18751035973568592723608225662866683144711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190962000000000000000000000000000000000000000
      center := (2864430)
      previous := (1432215)
      next := (1432215)
      square := (13770873176958857856094775657838000000000000)
      linear := (-1923426832929040521351789747537683400000000000)
      constant := (68953329812460268028205376276294098173340150991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree136.table
  base := (93755179867063432076438807687440053293821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1071046347883440141825445000997713000000000000)
      constant := (38480513607557719953707217640138859525394146989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580701030214860753791/100000000000000000000)
  centralHi := (4536726798553599639/781250000000000000)
  directionLo := (582847806594315898319/100000000000000000000)
  directionHi := (7285597582428948729/1250000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree137.table
  base := (23973023188337614678834630990190713247397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2799782913973382148780462430057313958000000000000)
      constant := (101128616994507957007917339565804436796385368178292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree137.table
  base := (95892092752686274119071950901684018572349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1078919662644808205108864883520533000000000000)
      constant := (39056330711303026482935174908340846753034050541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582847806594315898319/100000000000000000000)
  centralHi := (7285597582428948729/1250000000000000000)
  directionLo := (584986704815596232383/100000000000000000000)
  directionHi := (9140417262743691131/1562500000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree138.table
  base := (9805135537023802685473512573357469646553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (91980030)
      previous := (45990015)
      next := (45990015)
      square := (442198038682345546712376685012798000000000000)
      linear := (-62671423430317794315724192776059453400000000000)
      constant := (2280683954019538498312854027148566072787602289106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree138.table
  base := (98051355369672151508826492788525627998691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1086792977406176268392284766043353000000000000)
      constant := (39636436240652756729442502840436242387438112819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584986704815596232383/100000000000000000000)
  centralHi := (9140417262743691131/1562500000000000000)
  directionLo := (587117810980227348503/100000000000000000000)
  directionHi := (73389726372528418563/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree139.table
  base := (25058241929709334193973561771368379975941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2840645194755219339634714919788036848000000000000)
      constant := (104144044388128065619427331815271832380111142949876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree139.table
  base := (25058241929588811187575592412703673017941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1094666292167544331675704648566173000000000000)
      constant := (40220830195610456014202502160661980068189344276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587117810980227348503/100000000000000000000)
  centralHi := (73389726372528418563/12500000000000000000)
  directionLo := (147310302408177314641/25000000000000000000)
  directionHi := (117848241926541851713/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree140.table
  base := (51218464899738908633707398333502394456999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2861076335146137935061841164653398293000000000000)
      constant := (105668416366263546854921498729256843543335961037982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree140.table
  base := (102436929799067124882163004837216948810739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1102539606928912394959124531088993000000000000)
      constant := (40809512576179641974364353127324054609933130051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147310302408177314641/25000000000000000000)
  centralHi := (117848241926541851713/20000000000000000000)
  directionLo := (147839245949913209137/25000000000000000000)
  directionHi := (591356983799652836549/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree141.table
  base := (13082905201560723283469370666444293488867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-320167497281895170054329712168751082000000000000)
      constant := (11911543762810520061187956525352505937374277686936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree141.table
  base := (20932648322427187362604483771090303112441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-222082584338056091648508882722362600000000000)
      constant := (8280496676472759179852708376797771625719886569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147839245949913209137/25000000000000000000)
  centralHi := (591356983799652836549/100000000000000000000)
  directionLo := (74183151878457562739/12500000000000000000)
  directionHi := (593465215027660501913/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree142.table
  base := (106911903158183752580667274408074201935917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2901938615927975125916093654384121183000000000000)
      constant := (108750476885230366017570988119342755646887511121253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree142.table
  base := (5345595157894287366595425154603419127821/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-223657247290329704305192859226926600000000000)
      constant := (8399948522833271162692973066075259894108211956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74183151878457562739/12500000000000000000)
  centralHi := (593465215027660501913/100000000000000000000)
  directionLo := (148891495855000010617/25000000000000000000)
  directionHi := (595565983420000042469/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree143.table
  base := (27295728609222465537008006495396352577893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2922369756318893721343219899249482628000000000000)
      constant := (110308165426079382177543195435424240051031210572148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree143.table
  base := (6823932152289751930955991884597389608767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1126159551213016584809384178657453000000000000)
      constant := (42601290271590711021477062631628638301750545648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148891495855000010617/25000000000000000000)
  centralHi := (595565983420000042469/100000000000000000000)
  directionLo := (597659367672118241127/100000000000000000000)
  directionHi := (74707420959014780141/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree144.table
  base := (1741816803889335393905692240645984316453/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-326977877412201368530038460457204897000000000000)
      constant := (12430773276427819513328235383043566655854669724992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree144.table
  base := (27869068862175317627753205102626497962297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1134032865974384648092804061180273000000000000)
      constant := (43207126354640197873530184226377410067528035492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597659367672118241127/100000000000000000000)
  centralHi := (74707420959014780141/12500000000000000000)
  directionLo := (599745445106038853347/100000000000000000000)
  directionHi := (149936361276509713337/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree145.table
  base := (56895993097287392195022121793787142585197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-2963232037100730912197472388980205518000000000000)
      constant := (113456859070551851442652831065644320301285418569546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree145.table
  base := (113791986194390654603083952289796319697173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1141906180735752711376223943703093000000000000)
      constant := (43817250863318096549614707079333434155667308357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599745445106038853347/100000000000000000000)
  centralHi := (149936361276509713337/25000000000000000000)
  directionLo := (300912145851843737371/50000000000000000000)
  directionHi := (601824291703687474743/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree146.table
  base := (4645201866966586675090031475816171634167/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11037603600000000000000000000000000000000000000
      center := (165564054)
      previous := (82782027)
      next := (82782027)
      square := (795956469628221984082278033023036400000000000)
      linear := (-119346527099665980304983945353822678520000000000)
      constant := (4601914566967686656547905714846027362938748905503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree146.table
  base := (116130046674007853752009666198948459416091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1149779495497120774659643826225913000000000000)
      constant := (44431663797627628690919159938420082205945309419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300912145851843737371/50000000000000000000)
  centralHi := (601824291703687474743/100000000000000000000)
  directionLo := (120779196427836786911/20000000000000000000)
  directionHi := (150973995534795983639/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree147.table
  base := (29622614221996101631071729484183312433059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-333788257542507567005747208745658712000000000000)
      constant := (12961108310975502673592853855068758650037285308236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree147.table
  base := (118490456887850863747702973149273063984767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1157652810258488837943063708748733000000000000)
      constant := (45050365157571955734778729937456348935814393103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120779196427836786911/20000000000000000000)
  centralHi := (150973995534795983639/25000000000000000000)
  directionLo := (18936268431566907643/3125000000000000000)
  directionHi := (605960589810141044577/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree148.table
  base := (120873216836325623919430636613747186191049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3024525458273486698478851123576289853000000000000)
      constant := (118263190944321971369704484962851671908480481825441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree148.table
  base := (483492867344847614158696959262995234403/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (63654)
      previous := (31827)
      next := (31827)
      square := (306019403932419063468772792396400000000000)
      linear := (-46621045000794276049059343650862120000000000)
      constant := (1826934197726167113281150902259883324417814270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18936268431566907643/3125000000000000000)
  centralHi := (605960589810141044577/100000000000000000000)
  directionLo := (608018186868006818997/100000000000000000000)
  directionHi := (304009093434003409499/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree149.table
  base := (493113306077896777516944506266074096679/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11037603600000000000000000000000000000000000000
      center := (165564054)
      previous := (82782027)
      next := (82782027)
      square := (795956469628221984082278033023036400000000000)
      linear := (-121798263946576211756239094737666051920000000000)
      constant := (4795500504433095871274476706608041098989271961110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree149.table
  base := (61639163259688679241132409648537601132147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1173399439781224964509903473794373000000000000)
      constant := (46300633154377333244893495210566387820821895046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608018186868006818997/100000000000000000000)
  centralHi := (304009093434003409499/50000000000000000000)
  directionLo := (305034422123742826633/50000000000000000000)
  directionHi := (610068844247485653267/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree150.table
  base := (125705785937710215405974264879527426717837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-340598637672813765481455957034112527000000000000)
      constant := (13502548866478169923534058100597103769844314959837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree150.table
  base := (125705785937627760803514319018234494150981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1181272754542593027793323356317193000000000000)
      constant := (46932199791244398139780170094835899748447757429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305034422123742826633/50000000000000000000)
  centralHi := (610068844247485653267/100000000000000000000)
  directionLo := (153028157923768101107/25000000000000000000)
  directionHi := (612112631695072404429/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree151.table
  base := (64077797545654003251001061544641453955647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3085818879446242484760229858172374188000000000000)
      constant := (123169472506757938534355217236562464833075417837646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree151.table
  base := (128155595091237800518341527569574833002467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1189146069303961091076743238840013000000000000)
      constant := (47568054853758286703057070637460622403323172403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153028157923768101107/25000000000000000000)
  centralHi := (612112631695072404429/100000000000000000000)
  directionLo := (614149617796731846957/100000000000000000000)
  directionHi := (307074808898365923479/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree152.table
  base := (130627753980536135371654179449541898196103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3106250019837161080187356103037735633000000000000)
      constant := (124827110736198035309158515590711093210700349946927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree152.table
  base := (32656938495119090274275867261417394624539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1197019384065329154360163121362833000000000000)
      constant := (48208198341921851519461214507059884558286937004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614149617796731846957/100000000000000000000)
  centralHi := (307074808898365923479/50000000000000000000)
  directionLo := (616179870004754582463/100000000000000000000)
  directionHi := (9627810468824290351/1562500000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree153.table
  base := (133122262605657465502203188014906656452471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1202107328038477383934825969974278000000000000)
      constant := (48633546515429093846078428961421491843304264839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree153.table
  base := (66561131302803287560265967084354984232543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1204892698826697217643583003885653000000000000)
      constant := (48852630255737884162541585271405413055446097374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616179870004754582463/100000000000000000000)
  centralHi := (9627810468824290351/1562500000000000000)
  directionLo := (61820345466381915477/10000000000000000000)
  directionHi := (618203454663819154771/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree154.table
  base := (67819560483464610463195339341233496314077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3147112300618998271041608592768458523000000000000)
      constant := (128175703758064149730104137721055151343784215129386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree154.table
  base := (67819560483442947963980145342392033112931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1212766013588065280927002886408473000000000000)
      constant := (49501350595209115954775170628915456158590169958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61820345466381915477/10000000000000000000)
  centralHi := (618203454663819154771/100000000000000000000)
  directionLo := (620220437036288859917/100000000000000000000)
  directionHi := (310110218518144429959/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree155.table
  base := (8636145566537691540824165152401668957309/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3167543441009916866468734837633819968000000000000)
      constant := (129866658550504209609855432579907872827793082588496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree155.table
  base := (27635665812913236383997346236348895227429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-244127865669886668842084553786258600000000000)
      constant := (10030871872067643772386783360950908429467794261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620220437036288859917/100000000000000000000)
  centralHi := (310110218518144429959/50000000000000000000)
  directionLo := (311115440663385270033/50000000000000000000)
  directionHi := (622230881326770540067/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree156.table
  base := (17592485862365648478804330681806213829867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-354219397933426162432873453611020157000000000000)
      constant := (14618746540439782903739243777860939394268688414936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree156.table
  base := (140739886898893790728159411305755279999491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1228512643110801407493842651454113000000000000)
      constant := (50811656551127806492130918182172825765514600019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311115440663385270033/50000000000000000000)
  centralHi := (622230881326770540067/100000000000000000000)
  directionLo := (624234850705961507693/100000000000000000000)
  directionHi := (312117425352980753847/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree157.table
  base := (35830948617534101797368172850130359479517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3208405721791754057322987327364542858000000000000)
      constant := (133281884698432304400549313438888507306729109654612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree157.table
  base := (35830948617527420232219666150516582804333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1236385957872169470777262533976933000000000000)
      constant := (51473242167580435174903205899751862707884675188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624234850705961507693/100000000000000000000)
  centralHi := (312117425352980753847/50000000000000000000)
  directionLo := (4892440682295387959/781250000000000000)
  directionHi := (626232407333809658753/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree158.table
  base := (145930051778472268731729519032221793151711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3228836862182672652750113572229904303000000000000)
      constant := (135006156053933484069027129524408151884224451699399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree158.table
  base := (72965025889224759684992987001299488982339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1244259272633537534060682416499753000000000000)
      constant := (52139116209698605099839530249916406557227268902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4892440682295387959/781250000000000000)
  centralHi := (626232407333809658753/100000000000000000000)
  directionLo := (628223612382010797597/100000000000000000000)
  directionHi := (314111806191005398799/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree159.table
  base := (148558658824163155962551378904620081444751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-361029778063732360908582201899473972000000000000)
      constant := (15193503658940882482622957582582247297954688010751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree159.table
  base := (18569832353017974063481828332999715612029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1252132587394905597344102299022573000000000000)
      constant := (52809278677484761497755555436111298863424125288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628223612382010797597/100000000000000000000)
  centralHi := (314111806191005398799/50000000000000000000)
  directionLo := (63020852605586620973/10000000000000000000)
  directionHi := (630208526055866209731/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree160.table
  base := (75604807803717200634076494486313685783701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3269699142964509843604366061960627193000000000000)
      constant := (138488015328041897048180979998565006324677234894618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree160.table
  base := (151209615607417920429853061178978761245667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1260005902156273660627522181545393000000000000)
      constant := (53483729570941295850358173223366665678055281203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63020852605586620973/10000000000000000000)
  centralHi := (630208526055866209731/100000000000000000000)
  directionLo := (632187207615522578149/100000000000000000000)
  directionHi := (12643744152310451563/2000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree161.table
  base := (153882922128506399276095349444850130707111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3290130283355428439031492306825988638000000000000)
      constant := (140245603246661429754086684678187782546508197297999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree161.table
  base := (153882922128492372469966349428777250238149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1267879216917641723910942064068213000000000000)
      constant := (54162468890070547116811631239270530847776522741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632187207615522578149/100000000000000000000)
  centralHi := (12643744152310451563/2000000000000000000)
  directionLo := (634159715396615442787/100000000000000000000)
  directionHi := (158539928849153860697/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree162.table
  base := (156578578387594721245247762096494478313493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-367840158194038559384290950187927787000000000000)
      constant := (15779366298481387659620123680568589776003647851493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree162.table
  base := (156578578387582783521019250842796720931743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1275752531679009787194361946591033000000000000)
      constant := (54845496634874802967693907356609436412364861487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634159715396615442787/100000000000000000000)
  centralHi := (158539928849153860697/25000000000000000000)
  directionLo := (636126106830336547959/100000000000000000000)
  directionHi := (15903152670758413699/2500000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree163.table
  base := (15929658438491022970385805926062640381989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (827820270)
      previous := (413910135)
      next := (413910135)
      square := (3979782348141109920411390165115182000000000000)
      linear := (-666198512827453125977148959311342305600000000000)
      constant := (28758819129412178627633299755796539309453735807802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree163.table
  base := (159296584384900070311164208833293149181219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1283625846440377850477781829113853000000000000)
      constant := (55532812805356301018573970847544006019663552371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636126106830336547959/100000000000000000000)
  centralHi := (15903152670758413699/2500000000000000000)
  directionLo := (12761728769258892153/2000000000000000000)
  directionHi := (638086438462944607651/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree164.table
  base := (20254617515082399087407736298022947827737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3351423704528184225312871041422072973000000000000)
      constant := (145585000128852334121197433976643591473520841821064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree164.table
  base := (81018470060325273524997935462466938729281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1291499161201745913761201711636673000000000000)
      constant := (56224417401517230056901411327663435505957884258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12761728769258892153/2000000000000000000)
  centralHi := (638086438462944607651/100000000000000000000)
  directionLo := (128008153194947648169/20000000000000000000)
  directionHi := (320020382987369120423/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree165.table
  base := (164799645595043397144243712046601248972971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-374650538324344757859999698476381602000000000000)
      constant := (16376334459079153332840152803112559759077378058971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree165.table
  base := (16479964559503603996498399090908263012047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (318270)
      previous := (159135)
      next := (159135)
      square := (1530097019662095317343863961982000000000000)
      linear := (-259874495192622795408924318831898600000000000)
      constant := (11384062084671946251424691082988060524589613246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128008153194947648169/20000000000000000000)
  centralHi := (320020382987369120423/50000000000000000000)
  directionLo := (641989144198509086981/100000000000000000000)
  directionHi := (320994572099254543491/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree166.table
  base := (83792350404130130423391361100552868518801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3392285985310021416167123531152795863000000000000)
      constant := (149200125655646478310028460793225144665767222926418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree166.table
  base := (41896175202063500086347036263586955697727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1307245790724482040328041476682313000000000000)
      constant := (57620491870885899379967857954008274051988742972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641989144198509086981/100000000000000000000)
  centralHi := (320994572099254543491/50000000000000000000)
  directionLo := (128786325427498480631/20000000000000000000)
  directionHi := (160982906784373100789/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree167.table
  base := (170392105760502942894972775934587158523927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3412717125700940011594249776018157308000000000000)
      constant := (151024346700659959098213984302392253500218668353343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree167.table
  base := (85196052880248807895697453195569489203987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1315119105485850103611461359205133000000000000)
      constant := (58324961744097783952684998298146964421930196166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128786325427498480631/20000000000000000000)
  centralHi := (160982906784373100789/25000000000000000000)
  directionLo := (645868267982831768257/100000000000000000000)
  directionHi := (322934133991415884129/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree168.table
  base := (43305465112990113034978220246360633898209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (459900150)
      previous := (229950075)
      next := (229950075)
      square := (2210990193411727733561883425063990000000000000)
      linear := (-381460918454650956335708446764835417000000000000)
      constant := (16984408140750893096895139048326529045570170768836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree168.table
  base := (86610930225977959716702369933733692917657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1322992420247218166894881241727953000000000000)
      constant := (59033720042997390427755294979989825496326846226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell087.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645868267982831768257/100000000000000000000)
  centralHi := (322934133991415884129/50000000000000000000)
  directionLo := (161949779782643468259/25000000000000000000)
  directionHi := (647799119130573873037/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree169.table
  base := (176073964882817753578535026748102280260919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (4139101350)
      previous := (2069550675)
      next := (2069550675)
      square := (19898911740705549602056950825575910000000000000)
      linear := (-3453579406482777202448502265748880198000000000000)
      constant := (154706105353945818557345288478602485734565321234271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree169.table
  base := (176073964882813896942306409372756198816751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7650485098310476586719319809910000000000000)
      linear := (-1330865735008586230178301124250773000000000000)
      constant := (59746766767586681318161206895639747513246911359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell087.Kernel169
