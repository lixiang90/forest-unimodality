import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell002.Parameters
import ForestUnimodality.BinomialMassData.Q37_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_140.Batch100_149
import ForestUnimodality.BinomialMassData.Q19_70.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_70.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_70.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree000.table
  base := (2284692308644636927201787573/500000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (36196098611426470725849213800000000000000)
      constant := (6397138464204983396165005204400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree000.table
  base := (2284692308644636927201787573/500000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (18098049305713235362924606900000000000000)
      constant := (3198569232102491698082502602200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree001.table
  base := (34179943591846219574556596542500382653061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (154658772700701857005789463820000000000000)
      constant := (33442426276686847237968289052594874999999780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree001.table
  base := (33873983377667197010771414653000382653061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (75995414491171422582960204440000000000000)
      constant := (16570745044821268554332670204241187499999890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (28071884069766799937/100000000000000000000)
  directionHi := (14035942034883399969/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree002.table
  base := (25509940644890338083347777021910586734693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (55944855121418418930634431040000000000000)
      constant := (24917993623565017482977761336310374999999140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree002.table
  base := (25053934874692333104639662905685586734693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (25304483842350197625448160580000000000000)
      constant := (12235173435018321591871256427089937499999570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/100000000000000000000)
  centralHi := (14035942034883399969/50000000000000000000)
  directionLo := (7939927834565888721/20000000000000000000)
  directionHi := (19849819586414721803/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree003.table
  base := (18954936196815171677803714063731385896683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-42769062457865019144520601740000000000000)
      constant := (18492348177563670563429986024137258178749340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree003.table
  base := (9222027233977280496433084421006668501913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-25386446806471027332063883280000000000000)
      constant := (8996343159261943941133856469685535131874740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7939927834565888721/20000000000000000000)
  centralHi := (19849819586414721803/50000000000000000000)
  directionLo := (24310964736509743783/50000000000000000000)
  directionHi := (48621929473019487567/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree004.table
  base := (13974613478564151167604215848541836875363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-141482980037148457219675634520000000000000)
      constant := (13635979505007368672811175133043000137855740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree004.table
  base := (420766644552658720672855360749278702381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-76077377455292252289575927140000000000000)
      constant := (6570147546985422811299885482204690053334080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24310964736509743783/50000000000000000000)
  centralHi := (48621929473019487567/100000000000000000000)
  directionLo := (28071884069766799937/50000000000000000000)
  directionHi := (449150145116268799/800000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree005.table
  base := (10168201529148466219615074499886767442373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-240196897616431895294830667300000000000000)
      constant := (9956132064127077684649804944101532093525540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree005.table
  base := (1937870054624962975666399527283302529271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-126768308104113477247087971000000000000000)
      constant := (4747837251556812710540739510819091196713950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/50000000000000000000)
  centralHi := (449150145116268799/800000000000000000)
  directionLo := (62770641036492013613/100000000000000000000)
  directionHi := (31385320518246006807/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree006.table
  base := (7255646791037179140956197554058653673549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-338910815195715333369985700080000000000000)
      constant := (7178353368542478659923384842879480600078020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree006.table
  base := (85283338315809943366672168483701902311/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-177459238752934702204600014860000000000000)
      constant := (3384450503921716881628624471617114570591200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62770641036492013613/100000000000000000000)
  centralHi := (31385320518246006807/50000000000000000000)
  directionLo := (17190448022373068389/25000000000000000000)
  directionHi := (68761792089492273557/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree007.table
  base := (5010403000914470489781646721457545613059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-62517818967856967349305818980000000000000)
      constant := (725804011457724077946127900795556385828260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree007.table
  base := (4628364885659422250616898402874622036877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-32592881343107989594587436960000000000000)
      constant := (337755632431684574063262576758223542581390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17190448022373068389/25000000000000000000)
  centralHi := (68761792089492273557/100000000000000000000)
  directionLo := (37135612040819352983/50000000000000000000)
  directionHi := (74271224081638705967/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree008.table
  base := (407515893458732866924968666614052499209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-536338650354282209520295765640000000000000)
      constant := (3494060048223579557670497116382171593798560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree008.table
  base := (9151734992447130761965555615477771383/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-278841100050577152119624102580000000000000)
      constant := (1600188637861487565590706848010914552854400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/50000000000000000000)
  centralHi := (74271224081638705967/100000000000000000000)
  directionLo := (7939927834565888721/10000000000000000000)
  directionHi := (79399278345658887211/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree009.table
  base := (1882688356057851175548319447335739762823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-635052567933565647595450798420000000000000)
      constant := (2298961014860416499849248053053524967566540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree009.table
  base := (1598124080524583553572064345245176192521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-329532030699398377077136146440000000000000)
      constant := (1030842315390320082327236719041136334335290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7939927834565888721/10000000000000000000)
  centralHi := (79399278345658887211/100000000000000000000)
  directionLo := (84215652209300399811/100000000000000000000)
  directionHi := (21053913052325099953/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree010.table
  base := (786992926932052470068811787164584764813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-733766485512849085670605831200000000000000)
      constant := (1406059154951124286803773743571293069516740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree010.table
  base := (108917491828055302552825310508515330729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-380222961348219602034648190300000000000000)
      constant := (610933262689900643782232217745862560286050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84215652209300399811/100000000000000000000)
  centralHi := (21053913052325099953/25000000000000000000)
  directionLo := (44385545936330078969/50000000000000000000)
  directionHi := (88771091872660157939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree011.table
  base := (-94992351499911988955054242661473501127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-832480403092132523745760863980000000000000)
      constant := (748681920939171686776119204776255968895540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree011.table
  base := (-6010412674687801883777112954407566627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-430913891997040826992160234160000000000000)
      constant := (306913155849599350314623511508014617638500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44385545936330078969/50000000000000000000)
  centralHi := (88771091872660157939/100000000000000000000)
  directionLo := (5818994163610712597/6250000000000000000)
  directionHi := (93103906617771401553/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree012.table
  base := (-814162205106383848307089010932806058413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-931194320671415961820915896760000000000000)
      constant := (276952481473583885918150275253850062755260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree012.table
  base := (-987979845625223262005465823098666486227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-481604822645862051949672278020000000000000)
      constant := (93899967581770774512304652225653421748770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5818994163610712597/6250000000000000000)
  centralHi := (93103906617771401553/100000000000000000000)
  directionLo := (97243858946038975133/100000000000000000000)
  directionHi := (48621929473019487567/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree013.table
  base := (-704332641715198566066310759645072238477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1029908238250699399896070929540000000000000)
      constant := (-46514839997812459432555466603841587414920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree013.table
  base := (-311107075035617898683339117065881981899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-532295753294683276907184321880000000000000)
      constant := (-46601449450059669962910249852410855652550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97243858946038975133/100000000000000000000)
  centralHi := (48621929473019487567/50000000000000000000)
  directionLo := (101214617412424928111/100000000000000000000)
  directionHi := (6325913588276558007/6250000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree014.table
  base := (-476790412167986132869043519141354816267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-161231736547140405424460851760000000000000)
      constant := (-35686700633001455214232840493158697109520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree014.table
  base := (-253914450456423493492905513628139485939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-83283811991929214552099480820000000000000)
      constant := (-18339143151786795896594827183758112125840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101214617412424928111/100000000000000000000)
  centralHi := (6325913588276558007/6250000000000000000)
  directionLo := (52517686195152339567/50000000000000000000)
  directionHi := (21007074478060935827/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree015.table
  base := (-2331239230268779152353944434639283042229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1227336073409266276046380995100000000000000)
      constant := (-354079882675007339178946772133997381384420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree015.table
  base := (-609085969676438521471257290486510096107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-633677614592325726822208409600000000000000)
      constant := (-161719130609284304974415675278559788369720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52517686195152339567/50000000000000000000)
  centralHi := (21007074478060935827/20000000000000000000)
  directionLo := (54360969749436050507/50000000000000000000)
  directionHi := (21744387899774420203/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree016.table
  base := (-674301823169960279240104907054050076549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1326049990988549714121536027880000000000000)
      constant := (-375316853899565237221103426659876300072080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree016.table
  base := (-2786385670645162503925629822084616318739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-684368545241146951779720453460000000000000)
      constant := (-154361915539337423432619653045461996182110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54360969749436050507/50000000000000000000)
  centralHi := (21744387899774420203/20000000000000000000)
  directionLo := (28071884069766799937/25000000000000000000)
  directionHi := (112287536279067199749/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree017.table
  base := (-75435711163394961870143895807129409741/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1424763908567833152196691060660000000000000)
      constant := (-325633176522738569146052898518972861847200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree017.table
  base := (-1546654029156685815264046588296421195547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-735059475889968176737232497320000000000000)
      constant := (-112117225486108556597668796291492771636060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/25000000000000000000)
  centralHi := (112287536279067199749/100000000000000000000)
  directionLo := (115743343129742280607/100000000000000000000)
  directionHi := (3616979472804446269/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree018.table
  base := (-1650654392542490170009612445475919573029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1523477826147116590271846093440000000000000)
      constant := (-214246821927889866800481594934802363136840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree018.table
  base := (-168304064457143469700595560707705491013/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-785750406538789401694744541180000000000000)
      constant := (-39380481691516789346114179471513811927400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115743343129742280607/100000000000000000000)
  centralHi := (3616979472804446269/3125000000000000000)
  directionLo := (23819783503697666163/20000000000000000000)
  directionHi := (1860920586226380169/1562500000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree019.table
  base := (-3556034651104114531753893198918288239273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1622191743726400028347001126220000000000000)
      constant := (-48200406036212392954394582715422474487540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree019.table
  base := (-902879381497186352145784072265313783189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-836441337187610626652256585040000000000000)
      constant := (60510356045443967361078543810984984949560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23819783503697666163/20000000000000000000)
  centralHi := (1860920586226380169/1562500000000000000)
  directionLo := (122362505814902767779/100000000000000000000)
  directionHi := (6118125290745138389/5000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree020.table
  base := (-47339019217607362491339001077682362561/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1720905661305683466422156159000000000000000)
      constant := (167100888193213662080795994709702775217600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree020.table
  base := (-3834816508823135644461228282561028667821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-887132267836431851609768628900000000000000)
      constant := (185007415138427088116374031745095952767710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122362505814902767779/100000000000000000000)
  centralHi := (6118125290745138389/5000000000000000000)
  directionLo := (125541282072984027227/100000000000000000000)
  directionHi := (31385320518246006807/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree021.table
  base := (-3998823606108595842292195916954260815519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-259945654126423843499615884540000000000000)
      constant := (61069711698914291526295082929903485827340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree021.table
  base := (-4039969259218700063041829809668239717493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-133974742640750439509611524680000000000000)
      constant := (47450727859547027405129628996223219775490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125541282072984027227/100000000000000000000)
  centralHi := (31385320518246006807/25000000000000000000)
  directionLo := (128641533649731367493/100000000000000000000)
  directionHi := (64320766824865683747/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree022.table
  base := (-4194439723362754193825305602921838481789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-1918333496464250342572466224560000000000000)
      constant := (729727986225899992401552961134598287846780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree022.table
  base := (-846011465630824201840972341213493725747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-988514129134074301524792716620000000000000)
      constant := (500443435701095929528517448010940371919850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128641533649731367493/100000000000000000000)
  centralHi := (64320766824865683747/50000000000000000000)
  directionLo := (1053350459590163783/800000000000000000)
  directionHi := (32917201862192618219/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree023.table
  base := (-4376542594927227516581374374401042531459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2017047414043533780647621257340000000000000)
      constant := (1071299649552673323811831410907478319170180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree023.table
  base := (-440747510335177626526056434325829643739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1039205059782895526482304760480000000000000)
      constant := (688699187207262187862186384822434745678900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1053350459590163783/800000000000000000)
  centralHi := (32917201862192618219/25000000000000000000)
  directionLo := (67314013270283888557/50000000000000000000)
  directionHi := (26925605308113555423/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree024.table
  base := (-45471506997960006123564425758192826281/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2115761331622817218722776290120000000000000)
      constant := (1450224862458614929154781392289103024462000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree024.table
  base := (-2287047688161640174668229880904601508709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1089895990431716751439816804340000000000000)
      constant := (896004681694636852954428413529490521465180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67314013270283888557/50000000000000000000)
  centralHi := (26925605308113555423/20000000000000000000)
  directionLo := (17190448022373068389/12500000000000000000)
  directionHi := (137523584178984547113/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree025.table
  base := (-941571524641038971293619924561199294413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2214475249202100656797931322900000000000000)
      constant := (1864941911412325860619165277962623457376300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree025.table
  base := (-73928015740652540511089952863618460401/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1140586921080537976397328848200000000000000)
      constant := (1121637237599986552479411113571925081824640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17190448022373068389/12500000000000000000)
  centralHi := (137523584178984547113/100000000000000000000)
  directionLo := (28071884069766799937/20000000000000000000)
  directionHi := (70179710174416999843/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree026.table
  base := (-971985923847051310793341859841808446233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2313189166781384094873086355680000000000000)
      constant := (2314209867414968739255626559757138613458300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree026.table
  base := (-2440268798132216494109960264421241209179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1191277851729359201354840892060000000000000)
      constant := (1365023751081478389945796869563183615004580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/20000000000000000000)
  centralHi := (70179710174416999843/50000000000000000000)
  directionLo := (28627816931011070653/20000000000000000000)
  directionHi := (71569542327527676633/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree027.table
  base := (-1000875888383659850710753007427846479299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2411903084360667532948241388460000000000000)
      constant := (2797036231515072287336701674204052251434900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree027.table
  base := (-2511231591416439077139095480330773986827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1241968782378180426312352935920000000000000)
      constant := (1625706542577534922332077806054841492909540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28627816931011070653/20000000000000000000)
  centralHi := (71569542327527676633/50000000000000000000)
  directionLo := (145865788419058462699/100000000000000000000)
  directionHi := (1458657884190584627/1000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree028.table
  base := (-5142022416904424555832903055957439761671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-358659571705707281574770917320000000000000)
      constant := (473231712082219562324403875189958433366060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree028.table
  base := (-5157920888594856795586205775938802861549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-184665673289571664467123568540000000000000)
      constant := (271902508937022054904921649916283799691570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145865788419058462699/100000000000000000000)
  centralHi := (1458657884190584627/1000000000000000000)
  directionLo := (37135612040819352983/25000000000000000000)
  directionHi := (148542448163277411933/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree029.table
  base := (-1318379798671995258931817147606995877697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2609330919519234409098551454020000000000000)
      constant := (3860319689111901082633320586065076159427760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree029.table
  base := (-2643759428019280645349589021114528531391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1343350643675822876227377023640000000000000)
      constant := (2197558821207122510460863696538762039236820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/25000000000000000000)
  centralHi := (148542448163277411933/100000000000000000000)
  directionLo := (15117172216246788529/10000000000000000000)
  directionHi := (151171722162467885291/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree030.table
  base := (-2699704245838390988232706558757134946869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2708044837098517847173706486800000000000000)
      constant := (4439601403044507708860201605986015504136760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree030.table
  base := (-5411752703729412789940293784437758325521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1394041574324644101184889067500000000000000)
      constant := (2508187465424382937052953095225498420494710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15117172216246788529/10000000000000000000)
  centralHi := (151171722162467885291/100000000000000000000)
  directionLo := (153756041366812026281/100000000000000000000)
  directionHi := (76878020683406013141/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree031.table
  base := (-5520132283908072815373444338358031734219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2806758754677801285248861519580000000000000)
      constant := (5050033989856856286371884638973628900465380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree031.table
  base := (-5531028876539335995580121998420591556519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1444732504973465326142401111360000000000000)
      constant := (2835004337223692559998140937504910137305690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153756041366812026281/100000000000000000000)
  centralHi := (76878020683406013141/50000000000000000000)
  directionLo := (156297635721143389513/100000000000000000000)
  directionHi := (78148817860571694757/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree032.table
  base := (-70450691171970051952192387943126964529/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-2905472672257084723324016552360000000000000)
      constant := (5691260021620711223518821478186845980926400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree032.table
  base := (-2822841327034414152271382310060930166689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1495423435622286551099913155220000000000000)
      constant := (3177845149600807654803617274764288436644780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156297635721143389513/100000000000000000000)
  centralHi := (78148817860571694757/50000000000000000000)
  directionLo := (158798556691317774421/100000000000000000000)
  directionHi := (79399278345658887211/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree033.table
  base := (-718435018275074152373443798389481108379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3004186589836368161399171585140000000000000)
      constant := (6362982925860359644587040888866968110308640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree033.table
  base := (-5755992126357741032889544417208537348219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1546114366271107776057425199080000000000000)
      constant := (3536573638436201076599333950846816699372690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158798556691317774421/100000000000000000000)
  centralHi := (79399278345658887211/50000000000000000000)
  directionLo := (80630348322564147507/50000000000000000000)
  directionHi := (32252139329025659003/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree034.table
  base := (-11434881301552596414752138027262678203/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3102900507415651599474326617920000000000000)
      constant := (7064955365121069976244234039942678584862720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree034.table
  base := (-5862189111322273573980861351942109882283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1596805296919929001014937242940000000000000)
      constant := (3911076212950935122638694984244366157681330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80630348322564147507/50000000000000000000)
  centralHi := (32252139329025659003/20000000000000000000)
  directionLo := (163685805608484327053/100000000000000000000)
  directionHi := (81842902804242163527/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree035.table
  base := (-5957804013747545051793001996875606382043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-457373489284990719649925950100000000000000)
      constant := (1113852869940578344022834625824915106513980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree035.table
  base := (-2982233870650215491693929409034058877677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-235356603938392889424635612400000000000000)
      constant := (614465392614198187955977158860231757125220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163685805608484327053/100000000000000000000)
  centralHi := (81842902804242163527/50000000000000000000)
  directionLo := (16607550581866353663/10000000000000000000)
  directionHi := (166075505818663536631/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree036.table
  base := (-6057092476394212664914422066482426574107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3300328342574218475624636683480000000000000)
      constant := (8558852690476238004398859206719221957375140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree036.table
  base := (-1515747815853560852612657809872757786441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1698187158217571450929961330660000000000000)
      constant := (4707038253391762882582123066465394738575640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16607550581866353663/10000000000000000000)
  centralHi := (166075505818663536631/100000000000000000000)
  directionLo := (84215652209300399811/50000000000000000000)
  directionHi := (168431304418600799623/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree037.table
  base := (-192271092728100229380291854887563521789/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3399042260153501913699791716260000000000000)
      constant := (9350455821892649131238339729706507956696960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree037.table
  base := (-769737182892241410881648321076240516039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1748878088866392675887473374520000000000000)
      constant := (5128350213345693811686379950900137177127120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84215652209300399811/50000000000000000000)
  centralHi := (168431304418600799623/100000000000000000000)
  directionLo := (170754604574452985031/100000000000000000000)
  directionHi := (21344325571806623129/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree038.table
  base := (-1561169739118761791776013329258473775447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3497756177732785351774946749040000000000000)
      constant := (10171654563221014060922910488344782800247760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree038.table
  base := (-312465151000385081279362234053952196271/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1799569019515213900844985418380000000000000)
      constant := (5565136455188438666932668026255268476544200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170754604574452985031/100000000000000000000)
  centralHi := (21344325571806623129/12500000000000000000)
  directionLo := (21630839406174025123/12500000000000000000)
  directionHi := (34609343049878440197/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree039.table
  base := (-3166606426942586672783268828382928859257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3596470095312068789850101781820000000000000)
      constant := (11022342672697160417601557248413959435856280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree039.table
  base := (-1267461405931058912376136942629398516293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1850259950164035125802497462240000000000000)
      constant := (6017348422060444781765326515768973635082150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21630839406174025123/12500000000000000000)
  centralHi := (34609343049878440197/20000000000000000000)
  directionLo := (175308859826965546181/100000000000000000000)
  directionHi := (87654429913482773091/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree040.table
  base := (-6418369117571740551913037849669142926847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3695184012891352227925256814600000000000000)
      constant := (11902429541439776618445159445324239931689940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree040.table
  base := (-321099693528158736976748443373149750243/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1900950880812856350760009506100000000000000)
      constant := (6484944768505304480819638940143132447618600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175308859826965546181/100000000000000000000)
  centralHi := (87654429913482773091/50000000000000000000)
  directionLo := (44385545936330078969/25000000000000000000)
  directionHi := (177542183745320315877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree041.table
  base := (-6500226796367115183888909146003464595211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3793897930470635666000411847380000000000000)
      constant := (12811837701593143593663268933821104696693220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree041.table
  base := (-6503435552178458685258004144798209904207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-1951641811461677575717521549960000000000000)
      constant := (6967890209893930666008730868999877146938570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44385545936330078969/25000000000000000000)
  centralHi := (177542183745320315877/100000000000000000000)
  directionLo := (179747761277528873761/100000000000000000000)
  directionHi := (89873880638764436881/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree042.table
  base := (-16447134056083267858461610142774629673/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-556087406864274157725080982880000000000000)
      constant := (1964357253662641662771886150398620738312000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree042.table
  base := (-3290846824823901850052884393109020036051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-286047534587214114382147656260000000000000)
      constant := (1066593510629208751402167566316737194952860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179747761277528873761/100000000000000000000)
  centralHi := (89873880638764436881/50000000000000000000)
  directionLo := (181926601571924976841/100000000000000000000)
  directionHi := (90963300785962488421/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree043.table
  base := (-6654307743031256720435312200299524466611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-3991325765629202542150721912940000000000000)
      constant := (14718361779260099271430593577266966022721220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree043.table
  base := (-3328410453384379906990324538346017155283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2053023672759320025632545637680000000000000)
      constant := (7979712017576096747586795946159903187822660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181926601571924976841/100000000000000000000)
  centralHi := (90963300785962488421/50000000000000000000)
  directionLo := (23009956756103555613/12500000000000000000)
  directionHi := (36815930809765688981/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree044.table
  base := (-672663916127332938999400977036656458359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4090039683208485980225876945720000000000000)
      constant := (15715371709407848324291406236352766708081800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree044.table
  base := (-6728862570820950207376192840896431100423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2103714603408141250590057681540000000000000)
      constant := (8508540368241821770881761380736748760792730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23009956756103555613/12500000000000000000)
  centralHi := (36815930809765688981/20000000000000000000)
  directionLo := (37241562647108560621/20000000000000000000)
  directionHi := (93103906617771401553/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree045.table
  base := (-849486367576458793046579163342545930839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4188753600787769418301031978500000000000000)
      constant := (16741488363898636509519982421406939902222240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree045.table
  base := (-6797857509286437970189230248662264713393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2154405534056962475547569725400000000000000)
      constant := (9052620581335425415650622484730490290437430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37241562647108560621/20000000000000000000)
  centralHi := (93103906617771401553/50000000000000000000)
  directionLo := (188311923109476040841/100000000000000000000)
  directionHi := (94155961554738020421/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree046.table
  base := (-6862100216311016138227442785652215640359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4287467518367052856376187011280000000000000)
      constant := (17796675350173022003553187355722828672448180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree046.table
  base := (-6863839148016242629957576638320932948703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2205096464705783700505081769260000000000000)
      constant := (9611936278189908113399849742358742855135530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188311923109476040841/100000000000000000000)
  centralHi := (94155961554738020421/50000000000000000000)
  directionLo := (47598195252298985927/25000000000000000000)
  directionHi := (190392781009195943709/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree047.table
  base := (-6925299048288616635505834853444533218777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4386181435946336294451342044060000000000000)
      constant := (18880901249512099939722572325884857445598540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree047.table
  base := (-6926836262352071112042159948139884262237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2255787395354604925462593813120000000000000)
      constant := (10186473358887833470702588463870456711503870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47598195252298985927/25000000000000000000)
  centralHi := (190392781009195943709/100000000000000000000)
  directionLo := (192451141164821547097/100000000000000000000)
  directionHi := (96225570582410773549/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree048.table
  base := (-6985515142834778006496159795214009837879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4484895353525619732526497076840000000000000)
      constant := (19994138909751370271145554052498270358878580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree048.table
  base := (-6986873646477464675123989875139955572277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2306478326003426150420105856980000000000000)
      constant := (10776219674279266270805143897725421769584270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192451141164821547097/100000000000000000000)
  centralHi := (96225570582410773549/50000000000000000000)
  directionLo := (97243858946038975133/50000000000000000000)
  directionHi := (194487717892077950267/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree049.table
  base := (-7042772465375252708848486029917946831469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-654801324443557595800236015660000000000000)
      constant := (3019480692110513655617866497854987443594340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree049.table
  base := (-880496585176353127291868855131395745643/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-336738465236035339339659700120000000000000)
      constant := (1625880678237884240161841811039418382439920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97243858946038975133/50000000000000000000)
  centralHi := (194487717892077950267/100000000000000000000)
  directionLo := (196503188488367599559/100000000000000000000)
  directionHi := (4912579712209189989/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree050.table
  base := (-7097091762241319750773902163148235039621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4682323188684186608676807142400000000000000)
      constant := (22307558723174122466214239789864729661171420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree050.table
  base := (-7098151818236081707240585973788901427277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2407860187301068600335129944700000000000000)
      constant := (12001299538014478214558718669843438300634270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196503188488367599559/100000000000000000000)
  centralHi := (4912579712209189989/2500000000000000000)
  directionLo := (99249097932073609013/50000000000000000000)
  directionHi := (198498195864147218027/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree051.table
  base := (-7148491006104290041431519232088247222997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4781037106263470046751962175180000000000000)
      constant := (23507702931735066210837148150698017721462940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree051.table
  base := (-178735674753741226647803768581215458969/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2458551117949889825292641988560000000000000)
      constant := (12636616238060888852287706695179177004207600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99249097932073609013/50000000000000000000)
  centralHi := (198498195864147218027/100000000000000000000)
  directionLo := (200473350938591782611/100000000000000000000)
  directionHi := (50118337734647945653/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree052.table
  base := (-3598492888552150695484093950706092947419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4879751023842753484827117207960000000000000)
      constant := (24736782201919091769249876916104057823058760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree052.table
  base := (-449863247781282536148952163842532890047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2509242048598711050250154032420000000000000)
      constant := (13287108101803414787143397911978542142031520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200473350938591782611/100000000000000000000)
  centralHi := (50118337734647945653/25000000000000000000)
  directionLo := (202429234824849856223/100000000000000000000)
  directionHi := (6325913588276558007/3125000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree053.table
  base := (-7242589589604321721237497425498484731041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-4978464941422036922902272240740000000000000)
      constant := (25994783289650490578035908616791984963579820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree053.table
  base := (-362165932203748617624677271139079786219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2559932979247532275207666076280000000000000)
      constant := (13952769296876780726284335491236018095053800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202429234824849856223/100000000000000000000)
  centralHi := (6325913588276558007/3125000000000000000)
  directionLo := (204366400827045522531/100000000000000000000)
  directionHi := (51091600206761380633/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree054.table
  base := (-56916516975094815614494980204397889957/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5077178859001320360977427273520000000000000)
      constant := (27281694700305632978107651784182328683793920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree054.table
  base := (-3642978662661624893483249484184118438817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2610623909896353500165178120140000000000000)
      constant := (14633594778020366424336045680555563929959340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204366400827045522531/100000000000000000000)
  centralHi := (51091600206761380633/25000000000000000000)
  directionLo := (206285376268476820669/100000000000000000000)
  directionHi := (20628537626847682067/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree055.table
  base := (-3662584856073257441318302751717645230251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5175892776580603799052582306300000000000000)
      constant := (28597506452174124899238565687845915348708040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree055.table
  base := (-7325736919962809161192089799706901123063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2661314840545174725122690164000000000000000)
      constant := (15329580178492618304397431154618618449699130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206285376268476820669/100000000000000000000)
  centralHi := (20628537626847682067/10000000000000000000)
  directionLo := (208186664168129383341/100000000000000000000)
  directionHi := (104093332084064691671/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree056.table
  base := (-7362165057110439650579307029059969729923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-753515242022841033875391048440000000000000)
      constant := (4277458553249006216225506592267604237810780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree056.table
  base := (-184066628634000285663140663928124439121/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-387429395884856564297171743980000000000000)
      constant := (2291531673826288500043484382809251570461200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208186664168129383341/100000000000000000000)
  centralHi := (104093332084064691671/50000000000000000000)
  directionLo := (210070744780609358269/100000000000000000000)
  directionHi := (21007074478060935827/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree057.table
  base := (-7396307900521725687760741596666400885927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5373320611739170675202892371860000000000000)
      constant := (31315797423050930135555859195707427131791540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree057.table
  base := (-369837434412128699105916133177840052011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2762696701842817175037714251720000000000000)
      constant := (16767016116397988486472829678456167490292200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210070744780609358269/100000000000000000000)
  centralHi := (21007074478060935827/10000000000000000000)
  directionLo := (211938077012853782697/100000000000000000000)
  directionHi := (105969038506426891349/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree058.table
  base := (-3713802466599489021874059875905161749507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5472034529318454113278047404640000000000000)
      constant := (32718262546095551816594638502703882970966280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree058.table
  base := (-7427993345592172443673201225819054325667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2813387632491638399995226295580000000000000)
      constant := (17508460536813504211208266828652663380423170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211938077012853782697/100000000000000000000)
  centralHi := (105969038506426891349/50000000000000000000)
  directionLo := (13361818733091216989/6250000000000000000)
  directionHi := (8551563989178378873/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree059.table
  base := (-1491212395515417829501489564349910771547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5570748446897737551353202437420000000000000)
      constant := (34149599535890713976308197866149937219419700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree059.table
  base := (-372820207299099717466416763973913779423/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2864078563140459624952738339440000000000000)
      constant := (18265052514029704780823046342826644961654600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13361818733091216989/6250000000000000000)
  centralHi := (8551563989178378873/4000000000000000000)
  directionLo := (21562423295714977463/10000000000000000000)
  directionHi := (215624232957149774631/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree060.table
  base := (-935210512900839133388098100795523753849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5669462364477020989428357470200000000000000)
      constant := (35609803424276775627991799466163093769823840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree060.table
  base := (-3740992727067774059524479907414619453217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2914769493789280849910250383300000000000000)
      constant := (19036789909332071069534203075733672935847340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21562423295714977463/10000000000000000000)
  centralHi := (215624232957149774631/100000000000000000000)
  directionLo := (217443878997744202029/100000000000000000000)
  directionHi := (21744387899774420203/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree061.table
  base := (-7504475726656980604400756248307960898663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5768176282056304427503512502980000000000000)
      constant := (37098869883015988585822030270942698319310260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree061.table
  base := (-3752370530536535146854608528632687540983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-2965460424438102074867762427160000000000000)
      constant := (19823670865120687172313407336930966209836660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217443878997744202029/100000000000000000000)
  centralHi := (21744387899774420203/10000000000000000000)
  directionLo := (219248423457985323577/100000000000000000000)
  directionHi := (109624211728992661789/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree062.table
  base := (-7524440697974789562612835322766653522969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-5866890199635587865578667535760000000000000)
      constant := (38616795139062393002645766568806679547490380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree062.table
  base := (-7524674261866495964378395268941739995741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3016151355086923299825274471020000000000000)
      constant := (20625693766810304894536707877962547402086910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219248423457985323577/100000000000000000000)
  centralHi := (109624211728992661789/50000000000000000000)
  directionLo := (221038236203690505623/100000000000000000000)
  directionHi := (27629779525461313203/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree063.table
  base := (-1508316475109018371389706707339534303889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-852229159602124471950546081220000000000000)
      constant := (5737653700171248000222806726133825987277700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree063.table
  base := (-7541787922731987069637175739749080632351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-438120326533677789254683787840000000000000)
      constant := (3063265315707857840899938695254564355735430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221038236203690505623/100000000000000000000)
  centralHi := (27629779525461313203/12500000000000000000)
  directionLo := (111406836122458058949/50000000000000000000)
  directionHi := (222813672244916117899/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree064.table
  base := (-7555903690934898502279472329165089957439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6064318034794154741728977601320000000000000)
      constant := (41739209296489346787989482803050211841709780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree064.table
  base := (-7556084538941441968771306483675880322157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3117533216384565749740298558740000000000000)
      constant := (22275159971871556951551979776534818642143070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111406836122458058949/50000000000000000000)
  centralHi := (222813672244916117899/100000000000000000000)
  directionLo := (28071884069766799937/12500000000000000000)
  directionHi := (224575072558134399497/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree065.table
  base := (-1891851801270330186164432116730633253007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6163031952373438179804132634100000000000000)
      constant := (43343692815215856340804238497728417648212560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree065.table
  base := (-7567566284823925305420007086088641741017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3168224147033386974697810602600000000000000)
      constant := (23122600987138719414910717010391565546901670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/12500000000000000000)
  centralHi := (224575072558134399497/100000000000000000000)
  directionLo := (9052910594032640263/4000000000000000000)
  directionHi := (14145172803176000411/6250000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree066.table
  base := (-7576095156994431470526925579131659186451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6261745869952721617879287666880000000000000)
      constant := (44977024263148393231289163010392973997278020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree066.table
  base := (-378811752847429322945057253365434136841/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3218915077682208199655322646460000000000000)
      constant := (23985179326437609080510027483394745458958200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9052910594032640263/4000000000000000000)
  centralHi := (14145172803176000411/6250000000000000000)
  directionLo := (57014266068318475881/25000000000000000000)
  directionHi := (9122282570930956141/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree067.table
  base := (-7581969505983809924360029947369394452607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6360459787532005055954442699660000000000000)
      constant := (46639201720163569799860749385098493436445140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree067.table
  base := (-7582092511427468510895183050075718375793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3269606008331029424612834690320000000000000)
      constant := (24862894178273324838326484510401897995861430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57014266068318475881/25000000000000000000)
  centralHi := (9122282570930956141/4000000000000000000)
  directionLo := (229778274082147747601/100000000000000000000)
  directionHi := (114889137041073873801/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree068.table
  base := (-1896257992069750676496855379723193279021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6459173705111288494029597732440000000000000)
      constant := (48330223504356430378685225273533082346237680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree068.table
  base := (-7585140096145589603100451053332371754033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3320296938979850649570346734180000000000000)
      constant := (25755744833182207798927906382131137840523830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229778274082147747601/100000000000000000000)
  centralHi := (114889137041073873801/50000000000000000000)
  directionLo := (46297337251896912243/20000000000000000000)
  directionHi := (3616979472804446269/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree069.table
  base := (-3792642024397610295111187914701540363059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6557887622690571932104752765220000000000000)
      constant := (50050088140910068408445580650709480888404360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree069.table
  base := (-7585379078613432725309526288980706394333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3370987869628671874527858778040000000000000)
      constant := (26663730670084121297315930264750453866776830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46297337251896912243/20000000000000000000)
  centralHi := (3616979472804446269/1562500000000000000)
  directionLo := (233182582090994663961/100000000000000000000)
  directionHi := (116591291045497331981/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree070.table
  base := (-3791363534346711018647534794456259558993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-950943077181407910025701114000000000000000)
      constant := (7399827762155249228302320334402247323481960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree070.table
  base := (-7582810570040692672213799571793770478543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-488811257182499014212195831700000000000000)
      constant := (3940978734926616412013110665574436066501990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233182582090994663961/100000000000000000000)
  centralHi := (116591291045497331981/50000000000000000000)
  directionLo := (46973246541345167033/20000000000000000000)
  directionHi := (117433116353362917583/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree071.table
  base := (-7577362189296027251720339140669937613927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6755315457849138808255062830780000000000000)
      constant := (53576340948790487147272670727467961138351540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree071.table
  base := (-1515487109229487750838336986385840028489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3472369730926314324442882865760000000000000)
      constant := (28525105778285954597170016690165691930201950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46973246541345167033/20000000000000000000)
  centralHi := (117433116353362917583/50000000000000000000)
  directionLo := (118268949793549278243/50000000000000000000)
  directionHi := (236537899587098556487/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree072.table
  base := (-7569190432843777218818484164081258630821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6854029375428422246330217863560000000000000)
      constant := (55382726980225369890300972124848366541795420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree072.table
  base := (-189231371628944266263417427338471007831/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3523060661575135549400394909620000000000000)
      constant := (29478494150953231593696834143349968246512400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118268949793549278243/50000000000000000000)
  centralHi := (236537899587098556487/100000000000000000000)
  directionLo := (238197835036976661631/100000000000000000000)
  directionHi := (1860920586226380169/781250000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree073.table
  base := (-7558212700513943921084337710341621067163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-6952743293007705684405372896340000000000000)
      constant := (57217951546237666284356210142785711354180260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree073.table
  base := (-7558269283359892700295508349075308881397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3573751592223956774357906953480000000000000)
      constant := (30447015891906925747539357595272098648115470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238197835036976661631/100000000000000000000)
  centralHi := (1860920586226380169/781250000000000000)
  directionLo := (239846282630207078071/100000000000000000000)
  directionHi := (29980785328775884759/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree074.table
  base := (-943053723507965651716426914634895375751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7051457210586989122480527929120000000000000)
      constant := (59082013866985322431329139554404420254112160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree074.table
  base := (-3772239734281942598180351714757935329033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3624442522872777999315418997340000000000000)
      constant := (31430670673920097715180220527753223377547660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239846282630207078071/100000000000000000000)
  centralHi := (29980785328775884759/12500000000000000000)
  directionLo := (24148347762684634769/10000000000000000000)
  directionHi := (241483477626846347691/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree075.table
  base := (-7527842399413959719679142988909127224481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7150171128166272560555682961900000000000000)
      constant := (60974913252625916480758722875181555320008620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree075.table
  base := (-7527886011743099914204311762256957166097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3675133453521599224272931041200000000000000)
      constant := (32429458207415805126638128521369090988612470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24148347762684634769/10000000000000000000)
  centralHi := (241483477626846347691/100000000000000000000)
  directionLo := (30388705920637179729/12500000000000000000)
  directionHi := (243109647365097437833/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree076.table
  base := (-1877112789611550078638192515553167036849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7248885045745555998630837994680000000000000)
      constant := (62896649091755526614532215755463585215551920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree076.table
  base := (-7508489437106020418374983398886552031451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3725824384170420449230443085060000000000000)
      constant := (33443378235531891035284243050841589504589010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30388705920637179729/12500000000000000000)
  centralHi := (243109647365097437833/100000000000000000000)
  directionLo := (244725011629805535559/100000000000000000000)
  directionHi := (6118125290745138389/2500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree077.table
  base := (-7486256619249773362210219259091803432259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1049656994760691348100856146780000000000000)
      constant := (9263888691623801856581264846798647519483740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree077.table
  base := (-3743145105405862874225807172962269760603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-539502187831320239169707875560000000000000)
      constant := (4924632932835772387389272153282282233515580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244725011629805535559/100000000000000000000)
  centralHi := (6118125290745138389/2500000000000000000)
  directionLo := (246329782999203897863/100000000000000000000)
  directionHi := (30791222874900487233/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree078.table
  base := (-7461259275023941352395876086181488369253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7446312880904122874781148060240000000000000)
      constant := (66826628018123898385419139595060141398132060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree078.table
  base := (-1492257749702605282732952624000924656671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3827206245468062899145467172780000000000000)
      constant := (35516614886701475006437140914621734591156050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246329782999203897863/100000000000000000000)
  centralHi := (30791222874900487233/12500000000000000000)
  directionLo := (247924167171458516329/100000000000000000000)
  directionHi := (24792416717145851633/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree079.table
  base := (-7433459565813007473830466419578726650161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7545026798483406312856303093020000000000000)
      constant := (68834870190783965657636761399297347882842220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree079.table
  base := (-7433485421886259713435581903005770659891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3877897176116884124102979216640000000000000)
      constant := (36575931123963690642704586006658172376653410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247924167171458516329/100000000000000000000)
  centralHi := (24792416717145851633/10000000000000000000)
  directionLo := (49901672654486336661/20000000000000000000)
  directionHi := (124754181636215841653/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree080.table
  base := (-3701428942614287689082593121505609106853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7643740716062689750931458125800000000000000)
      constant := (70871946973607443234103547276249006150568120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree080.table
  base := (-3701440282142542240431917193253569493733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3928588106765705349060491260500000000000000)
      constant := (37650379078293760792308356140211501896141660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49901672654486336661/20000000000000000000)
  centralHi := (124754181636215841653/50000000000000000000)
  directionLo := (50216512829193610891/20000000000000000000)
  directionHi := (31385320518246006807/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree081.table
  base := (-7369454586292710182490389903954139256403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7742454633641973189006613158580000000000000)
      constant := (72937858020632707300070949965389443528725060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree081.table
  base := (-7369474475636928786459873596690596100479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-3979279037414526574018003304360000000000000)
      constant := (38739958602727245700698378332452607910765290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50216512829193610891/20000000000000000000)
  centralHi := (31385320518246006807/12500000000000000000)
  directionLo := (252646956627901199433/100000000000000000000)
  directionHi := (126323478313950599717/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree082.table
  base := (-3666624993259005375894042894974823119757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7841168551221256627081768191360000000000000)
      constant := (75032603020697410967856601246927346685276280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree082.table
  base := (-3666633713342305000528386212729695225131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4029969968063347798975515348220000000000000)
      constant := (39844669564600164856166446866348898679371620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252646956627901199433/100000000000000000000)
  centralHi := (126323478313950599717/50000000000000000000)
  directionLo := (127100860902441389443/50000000000000000000)
  directionHi := (254201721804882778887/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree083.table
  base := (-7294244372325230537769426402074915013733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-7939882468800540065156923224140000000000000)
      constant := (77156181693109215854783571669807083286541660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree083.table
  base := (-3647129831330856993891601716625993742999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4080660898712169023933027392080000000000000)
      constant := (40964511843748061185779512187285526131860980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127100860902441389443/50000000000000000000)
  centralHi := (254201721804882778887/100000000000000000000)
  directionLo := (255747035259049374331/100000000000000000000)
  directionHi := (63936758814762343583/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree084.table
  base := (-1813109500721439308938633750886999345099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1148370912339974786176011179560000000000000)
      constant := (11329799111982880288491162919439280366744560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree084.table
  base := (-7252451406478287000209952329786742230027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-590193118480141464127219919420000000000000)
      constant := (6014212190135001717898269899642928043898110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255747035259049374331/100000000000000000000)
  centralHi := (63936758814762343583/25000000000000000000)
  directionLo := (257283067299462734987/100000000000000000000)
  directionHi := (64320766824865683747/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree085.table
  base := (-7207831113464706081818332551158050137391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8137310303959106941307233289700000000000000)
      constant := (81489839062450436530466885008077610865356820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree085.table
  base := (-7207842861482999917714864947272083969517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4182042760009811473848051479800000000000000)
      constant := (43249589926550168643796433739211678854936670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257283067299462734987/100000000000000000000)
  centralHi := (64320766824865683747/25000000000000000000)
  directionLo := (258809983181187000253/100000000000000000000)
  directionHi := (129404991590593500127/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree086.table
  base := (-3580211959165180404714874917287926302101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8236024221538390379382388322480000000000000)
      constant := (83699917318837121329070253211937664447882040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree086.table
  base := (-895054276732370690050773298562881156763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4232733690658632698805563523660000000000000)
      constant := (44414825539333805779052105412049505865489040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258809983181187000253/100000000000000000000)
  centralHi := (129404991590593500127/50000000000000000000)
  directionLo := (130163971656400302253/50000000000000000000)
  directionHi := (260327943312800604507/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree087.table
  base := (-7110216613287005231443334671088771508433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8334738139117673817457543355260000000000000)
      constant := (85938828361152018278650788186713503921735660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree087.table
  base := (-1422045126940526454077332158788662747531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4283424621307453923763075567520000000000000)
      constant := (45595192085458663684624559687186776268549050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130163971656400302253/50000000000000000000)
  centralHi := (260327943312800604507/100000000000000000000)
  directionLo := (261837103453080445989/100000000000000000000)
  directionHi := (26183710345308044599/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree088.table
  base := (-7057209377880649845388630437430138297093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8433452056696957255532698388040000000000000)
      constant := (88206572013440037091629537423206464468848860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree088.table
  base := (-56457738254627806264044234054082303321/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4334115551956275148720587611380000000000000)
      constant := (46790689487595649308992668428971458921588750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261837103453080445989/100000000000000000000)
  centralHi := (26183710345308044599/10000000000000000000)
  directionLo := (1053350459590163783/400000000000000000)
  directionHi := (263337614897540945751/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree089.table
  base := (-7001402377320618342504245210742235091659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8532165974276240693607853420820000000000000)
      constant := (90503148113796040550592665005817109610174180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree089.table
  base := (-7001409301336417982821748140516223446979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4384806482605096373678099655240000000000000)
      constant := (48001317674155800909122543019258050510980290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1053350459590163783/400000000000000000)
  centralHi := (263337614897540945751/100000000000000000000)
  directionLo := (2118636997243682703/800000000000000000)
  directionHi := (66207406163865084469/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree090.table
  base := (-1735698941038571393364429630524710727391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8630879891855524131683008453600000000000000)
      constant := (92828556512723601301885982194093133948627280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree090.table
  base := (-2777120731589559878064398171970821749/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4435497413253917598635611699100000000000000)
      constant := (49227076578622872480604601245535743357475000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2118636997243682703/800000000000000000)
  centralHi := (66207406163865084469/25000000000000000000)
  directionLo := (133156637808990236907/50000000000000000000)
  directionHi := (53262655123596094763/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree091.table
  base := (-6881389679727336303362892349628426018903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1247084829919258224251166212340000000000000)
      constant := (13597542438814849753671131978495520357353580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree091.table
  base := (-3440697495660103980338493746605084630647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-640884049128962689084731963280000000000000)
      constant := (7209709448424716196216931726768288151709420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133156637808990236907/50000000000000000000)
  centralHi := (53262655123596094763/20000000000000000000)
  directionLo := (133894353358912096573/50000000000000000000)
  directionHi := (267788706717824193147/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree092.table
  base := (-6817184255457643263867938990243429565137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8828307727014091007833318519160000000000000)
      constant := (97565869661947566195013281120969439026165740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree092.table
  base := (-6817188906816922155914137649444857560643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4536879274551560048550635786820000000000000)
      constant := (51723986297169849693357543018436019795284930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133894353358912096573/50000000000000000000)
  centralHi := (267788706717824193147/100000000000000000000)
  directionLo := (269256053081135554229/100000000000000000000)
  directionHi := (26925605308113555423/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree093.table
  base := (-6750179613947157165967107082980759613927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-8927021644593374445908473551940000000000000)
      constant := (99977774163304543363057690342339355578351540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree093.table
  base := (-6750183686665113165265237348603076364731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4587570205200381273508147830680000000000000)
      constant := (52995136998724856706769196228223492581281810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269256053081135554229/100000000000000000000)
  centralHi := (26925605308113555423/10000000000000000000)
  directionLo := (135357723085956305381/50000000000000000000)
  directionHi := (270715446171912610763/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree094.table
  base := (-3340187934976492783956515047104752479251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9025735562172657883983628584720000000000000)
      constant := (102418510463312914372743570716536685140668040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree094.table
  base := (-66803794356071383828907250660565961847/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4638261135849202498465659874540000000000000)
      constant := (54281418192314279290614866863808267869497000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135357723085956305381/50000000000000000000)
  centralHi := (270715446171912610763/100000000000000000000)
  directionLo := (850521918529592741/312500000000000000)
  directionHi := (272167013929469677121/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree095.table
  base := (-3303886565618023428369641627297264102781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9124449479751941322058783617500000000000000)
      constant := (104888078456366979204778018517509862358549240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree095.table
  base := (-6607776252608462633909585185832319230807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4688952066498023723423171918400000000000000)
      constant := (55582829829445039680586252577017163576904570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (850521918529592741/312500000000000000)
  centralHi := (272167013929469677121/100000000000000000000)
  directionLo := (136805440449667944017/50000000000000000000)
  directionHi := (54722176179867177607/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree096.table
  base := (-653237149930326378878185332677664055979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9223163397331224760133938650280000000000000)
      constant := (107386478042989953557951766717870892251405800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree096.table
  base := (-1306474846290569943168763857904305813699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4739642997146844948380683962260000000000000)
      constant := (56899371864163093615897572592870450756437450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136805440449667944017/50000000000000000000)
  centralHi := (54722176179867177607/20000000000000000000)
  directionLo := (11001886734318763769/4000000000000000000)
  directionHi := (137523584178984547113/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree097.table
  base := (-258166842802286368440508673024159688617/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9321877314910508198209093683060000000000000)
      constant := (109913709129197365042232278333068587628883500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree097.table
  base := (-1613543365315616676138251947041712492319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4790333927795666173338196006120000000000000)
      constant := (58231044252798579229377632509957243515054760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11001886734318763769/4000000000000000000)
  centralHi := (137523584178984547113/50000000000000000000)
  directionLo := (138237997215819267633/50000000000000000000)
  directionHi := (276475994431638535267/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree098.table
  base := (-1593292983591223099460631644351735962783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1345798747498541662326321245120000000000000)
      constant := (16067110232277056795528159084757027860841520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree098.table
  base := (-1274634805390577005041865546110513145007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-691574979777783914042244007140000000000000)
      constant := (8511120993391838074670295082053320399247550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138237997215819267633/50000000000000000000)
  centralHi := (276475994431638535267/100000000000000000000)
  directionLo := (69474368552451526309/25000000000000000000)
  directionHi := (277897474209806105237/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree099.table
  base := (-6289374178557191150775649736003242076821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9519305150069075074359403748620000000000000)
      constant := (115054665448611937891871992687821322764715420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree099.table
  base := (-3144688004815807682510657030746425017509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4891715789093308623253220093840000000000000)
      constant := (60939779927253275259108689663159503482841180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69474368552451526309/25000000000000000000)
  centralHi := (277897474209806105237/100000000000000000000)
  directionLo := (139655859926657102329/50000000000000000000)
  directionHi := (279311719853314204659/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree100.table
  base := (-6202777884866260553935538432482591099793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9618019067648358512434558781400000000000000)
      constant := (117668390516627425029315932528167060722202860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree100.table
  base := (-620277948694764912066850375939487797237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4942406719742129848210732137700000000000000)
      constant := (62316843135281799654254531656896509793538700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139655859926657102329/50000000000000000000)
  centralHi := (279311719853314204659/100000000000000000000)
  directionLo := (28071884069766799937/10000000000000000000)
  directionHi := (280718840697667999371/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree101.table
  base := (-6113383131810556411964319471589235306847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9716732985227641950509713814180000000000000)
      constant := (120310946753037772292479648845687049399289940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree101.table
  base := (-1222676906679694489674898102743075147077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-4993097650390951073168244181560000000000000)
      constant := (63709036541324671491580030647750465889661350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28071884069766799937/10000000000000000000)
  centralHi := (280718840697667999371/100000000000000000000)
  directionLo := (282118943351681243493/100000000000000000000)
  directionHi := (141059471675840621747/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree102.table
  base := (-1505297498633318983615939891946569844327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9815446902806925388584868846960000000000000)
      constant := (122982334084202646415953410260207446210238160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree102.table
  base := (-6021191220600148704704920663707482222403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5043788581039772298125756225420000000000000)
      constant := (65116360110290019726368019929487333711022530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282118943351681243493/100000000000000000000)
  centralHi := (141059471675840621747/50000000000000000000)
  directionLo := (283512131791737542803/100000000000000000000)
  directionHi := (70878032947934385701/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree103.table
  base := (-5926198545100519364669060994661545879693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-9914160820386208826660023879740000000000000)
      constant := (125682552439497269161366718543612185037900860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree103.table
  base := (-1481549904381328156878167481244354555623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5094479511688593523083268269280000000000000)
      constant := (66538813808381253337070590401460065070978920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283512131791737542803/100000000000000000000)
  centralHi := (70878032947934385701/25000000000000000000)
  directionLo := (28489850745190292163/10000000000000000000)
  directionHi := (284898507451902921631/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree104.table
  base := (-5828408852764295925301431183189171663519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10012874737965492264735178912520000000000000)
      constant := (128411601751054671490452790413546611769751380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree104.table
  base := (-5828409790713269018692997867971011309147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5145170442337414748040780313140000000000000)
      constant := (67976397602994112970759064874150204458517970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28489850745190292163/10000000000000000000)
  centralHi := (284898507451902921631/100000000000000000000)
  directionLo := (28627816931011070653/10000000000000000000)
  directionHi := (286278169310110706531/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree105.table
  base := (-22911283936779480025793192704486296337/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1444512665077825100401476277900000000000000)
      constant := (18738497421933999185846563769730479628205000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree105.table
  base := (-2863910902227913067597545880369360953449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-742265910426605138999756051000000000000000)
      constant := (9918444494660801797361191655173289466517140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28627816931011070653/10000000000000000000)
  centralHi := (286278169310110706531/100000000000000000000)
  directionLo := (287651213970625958553/100000000000000000000)
  directionHi := (143825606985312979277/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree106.table
  base := (-140610875092158883906618235161551020363/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10210302573124059140885488978080000000000000)
      constant := (133956192983939006119594220382969200001770400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree106.table
  base := (-5624435720962007530353432355069602324539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5246552303635057197955804400860000000000000)
      constant := (70896955356793330628244524969271894860975890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287651213970625958553/100000000000000000000)
  centralHi := (143825606985312979277/50000000000000000000)
  directionLo := (72254433935745971661/25000000000000000000)
  directionHi := (57803547148596777329/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree107.table
  base := (-220730038933558174425524280592267185577/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10309016490703342578960644010860000000000000)
      constant := (136771734781399508608287977900329953953363500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree107.table
  base := (-689781450063045674243457920438019813557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5297243234283878422913316444720000000000000)
      constant := (72379929255963716537915589604181962330856560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72254433935745971661/25000000000000000000)
  centralHi := (57803547148596777329/20000000000000000000)
  directionLo := (58075565343516955799/20000000000000000000)
  directionHi := (72594456679396194749/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree108.table
  base := (-21129956848518734679355868891604974209/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10407730408282626017035799043640000000000000)
      constant := (139616107287052735289827480933802144070446080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree108.table
  base := (-676158687693656824696662390784745175487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5347934164932699647870828488580000000000000)
      constant := (73878033131488256423459733464227798912090960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58075565343516955799/20000000000000000000)
  centralHi := (72594456679396194749/25000000000000000000)
  directionLo := (291731576838116925399/100000000000000000000)
  directionHi := (1458657884190584627/500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree109.table
  base := (-5297489001511941647928421074608276986363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10506444325861909455110954076420000000000000)
      constant := (142489310443882226247176678187648388553364260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree109.table
  base := (-82773273138642374279013738651388891927/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5398625095581520872828340532440000000000000)
      constant := (75391266955546496246689952130563444349169280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291731576838116925399/100000000000000000000)
  centralHi := (1458657884190584627/500000000000000000)
  directionLo := (29307907397096870651/10000000000000000000)
  directionHi := (293079073970968706511/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree110.table
  base := (-5182911174632791313698584327735740454757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10605158243441192893186109109200000000000000)
      constant := (145391344196595989242175458691968974354338140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree110.table
  base := (-5182911593666512982081146498730131969457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5449316026230342097785852576300000000000000)
      constant := (76919630701095054003157701683622235334966070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29307907397096870651/10000000000000000000)
  centralHi := (293079073970968706511/100000000000000000000)
  directionLo := (7360510099294535893/2500000000000000000)
  directionHi := (294420403971781435721/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree111.table
  base := (-1266383881839709222753266064676965007781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10703872161020476331261264141980000000000000)
      constant := (148322208491514042295352099824950797169498480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree111.table
  base := (-63319198670344287267937001956467739851/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5500006956879163322743364620160000000000000)
      constant := (78463124341821867896260441039397464597840800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7360510099294535893/2500000000000000000)
  centralHi := (294420403971781435721/100000000000000000000)
  directionLo := (59151130149857120323/20000000000000000000)
  directionHi := (18484728171830350101/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree112.table
  base := (-4945362112923451291343331010616306347591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1543226582657108538476631310680000000000000)
      constant := (21611700468066811421923508692337717111337260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree112.table
  base := (-4945362433045815470305449730472085523149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-792956841075426363957268094860000000000000)
      constant := (11431678264586432471712639535858954013379570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59151130149857120323/20000000000000000000)
  centralHi := (18484728171830350101/6250000000000000000)
  directionLo := (37135612040819352983/12500000000000000000)
  directionHi := (59416979265310964773/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree113.table
  base := (-2411195491555093805036121420926358469139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-10901299996179043207411574207540000000000000)
      constant := (154270428500709020183037640662984837400487560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree113.table
  base := (-602798907859786844371953377169114040157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5601388818176805772658388707880000000000000)
      constant := (81595501206975619710263133038056072962584560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37135612040819352983/12500000000000000000)
  centralHi := (59416979265310964773/20000000000000000000)
  directionLo := (14920411044990202859/5000000000000000000)
  directionHi := (298408220899804057181/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree114.table
  base := (-4696622188335869963365677063861556146001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11000013913758326645486729240320000000000000)
      constant := (157287784114829575350228779509597674976919020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree114.table
  base := (-4696622432817926826674823196455405835741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5652079748825626997615900751740000000000000)
      constant := (83184384382084101585382037622672851140486910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14920411044990202859/5000000000000000000)
  centralHi := (298408220899804057181/100000000000000000000)
  directionLo := (299725702894851314999/100000000000000000000)
  directionHi := (59945140578970263/20000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree115.table
  base := (-4568055777725592899274267744997303383997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11098727831337610083561884273100000000000000)
      constant := (160333970070686752797948355999215142683682940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree115.table
  base := (-4568055991355950739213722014214639669821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5702770679474448222573412795600000000000000)
      constant := (84788397353669765790977955469109826561787710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299725702894851314999/100000000000000000000)
  centralHi := (59945140578970263/20000000000000000)
  directionLo := (301037419021355398317/100000000000000000000)
  directionHi := (150518709510677699159/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree116.table
  base := (-4436691799180602529248611876962502518961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11197441748916893521637039305880000000000000)
      constant := (163408986321337331336974785079968747531418220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree116.table
  base := (-4436691985838648313521037957418102353857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5753461610123269447530924839460000000000000)
      constant := (86407540098532934234795816478841129846610070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301037419021355398317/100000000000000000000)
  centralHi := (150518709510677699159/50000000000000000000)
  directionLo := (15117172216246788529/5000000000000000000)
  directionHi := (302343444324935770581/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree117.table
  base := (-4302530299439907667508560925538375303871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11296155666496176959712194338660000000000000)
      constant := (166512832820977082329372612315392892202206420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree117.table
  base := (-2151265231259595524983848228058379092539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5804152540772090672488436883320000000000000)
      constant := (88041812594009552881653867191141788489311780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15117172216246788529/5000000000000000000)
  centralHi := (302343444324935770581/100000000000000000000)
  directionLo := (60728770447454956867/20000000000000000000)
  directionHi := (18977740764829674021/6250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree118.table
  base := (-1041392831034090186858646705686865576743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11394869584075460397787349371440000000000000)
      constant := (169645509524885810390428975212105486939167440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree118.table
  base := (-4165571466605157429685922046163638194333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5854843471420911897445948927180000000000000)
      constant := (89691214817947908275797317583443817284776830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60728770447454956867/20000000000000000000)
  centralHi := (18977740764829674021/6250000000000000000)
  directionLo := (60987742924859381973/20000000000000000000)
  directionHi := (152469357312148454933/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree119.table
  base := (-1006453729461963488423713189360661887881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1641940500236391976551786343460000000000000)
      constant := (24686716627053883025595581977861529342786640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree119.table
  base := (-4025815042302219558768183901053422165463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-843647771724247588914780138720000000000000)
      constant := (13050820964098174440748693965819260448417590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60987742924859381973/20000000000000000000)
  centralHi := (152469357312148454933/50000000000000000000)
  directionLo := (306228101832514412889/100000000000000000000)
  directionHi := (30622810183251441289/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree120.table
  base := (-194163056207209699892799524040171628789/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11592297419234027273937659437000000000000000)
      constant := (175997353371752784118257609098012636075735600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree120.table
  base := (-3883261232854433804093747314579833566659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-5956225332718554347360973014900000000000000)
      constant := (93035408365037903690213647729055881552337090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306228101832514412889/100000000000000000000)
  centralHi := (30622810183251441289/10000000000000000000)
  directionLo := (307512082733624052563/100000000000000000000)
  directionHi := (76878020683406013141/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree121.table
  base := (-3737909985630147652006389922550179965247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11691011336813310712012814469780000000000000)
      constant := (179216520430259947771047958839925323634057940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree121.table
  base := (-3737910080581514346466107230912008826551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6006916263367375572318485058760000000000000)
      constant := (94730199646263296142121974965764115674990010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307512082733624052563/100000000000000000000)
  centralHi := (76878020683406013141/25000000000000000000)
  directionLo := (308790724767434799307/100000000000000000000)
  directionHi := (77197681191858699827/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree122.table
  base := (-3589761543985088131860819651215813675903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11789725254392594150087969502560000000000000)
      constant := (182464517524052886386139649873606502597615060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree122.table
  base := (-358976162691342027734672085657176714999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6057607194016196797275997102620000000000000)
      constant := (96440120572062718486149725439663834096504900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308790724767434799307/100000000000000000000)
  centralHi := (77197681191858699827/25000000000000000000)
  directionLo := (310064093983202283049/100000000000000000000)
  directionHi := (6201281879664045661/2000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree123.table
  base := (-859703959999904616530332770403896753919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11888439171971877588163124535340000000000000)
      constant := (185741344613156808995404671812537224724637520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree123.table
  base := (-859703978105636247080171780299369145141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6108298124665018022233509146480000000000000)
      constant := (98165171122555697960420200675232236475523640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310064093983202283049/100000000000000000000)
  centralHi := (6201281879664045661/2000000000000000000)
  directionLo := (311332255079441656717/100000000000000000000)
  directionHi := (155666127539720828359/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree124.table
  base := (-3285072913609501041916712685735328141563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-11987153089551161026238279568120000000000000)
      constant := (189047001658434668459456811954171378421268260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree124.table
  base := (-657014595370752056343918346241490783241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6158989055313839247191021190340000000000000)
      constant := (99905351278267247381790923676324347581059550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311332255079441656717/100000000000000000000)
  centralHi := (155666127539720828359/50000000000000000000)
  directionLo := (156297635721143389513/50000000000000000000)
  directionHi := (312595271442286779027/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree125.table
  base := (-125141312157087266252708308016110286123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-12085867007130444464313434600900000000000000)
      constant := (192381488621556267897166741926417797989986500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree125.table
  base := (-1564266429576268059047219880477577330467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6209679985962660472148533234200000000000000)
      constant := (101660661020114086469591901956506974216142340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156297635721143389513/50000000000000000000)
  centralHi := (312595271442286779027/100000000000000000000)
  directionLo := (313853205182460068069/100000000000000000000)
  directionHi := (31385320518246006807/10000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree126.table
  base := (-593839109854232166400006921343718662603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1400000000000000000000000000000000000000000
      center := (1751)
      previous := (629)
      next := (0)
      square := (26679437183590118398690549400000000000000)
      linear := (-1740654417815675414626941376240000000000000)
      constant := (27963543637852782399473179659685396936177900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree126.table
  base := (-46393681210802024442430425398855414143/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (867)
      previous := (323)
      next := (0)
      square := (13339718591795059199345274700000000000000)
      linear := (-894338702373068813872292182580000000000000)
      constant := (14775871475627387323008097238341127744639360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313853205182460068069/100000000000000000000)
  centralHi := (31385320518246006807/10000000000000000000)
  directionLo := (78776529292728509351/25000000000000000000)
  directionHi := (63021223434182807481/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree127.table
  base := (-43860331049897409020633714560706501301/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-12283294842289011340463744666460000000000000)
      constant := (199136952151873339460703631987652988238401280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree127.table
  base := (-140353061464720637773390199733281975227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6311061847260302922063557321920000000000000)
      constant := (105216669187762228409993663775792836642775400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78776529292728509351/25000000000000000000)
  centralHi := (63021223434182807481/20000000000000000000)
  directionLo := (316354067073202384961/100000000000000000000)
  directionHi := (158177033536601192481/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree128.table
  base := (-2642129754505196585015287731506578067187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-12382008759868294778538899699240000000000000)
      constant := (202557928646192884895459574593491553494156740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree128.table
  base := (-528425958252257810111838547819816872251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6361752777909124147021069365780000000000000)
      constant := (107017367577242881270488939770065448662985050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell002.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316354067073202384961/100000000000000000000)
  centralHi := (158177033536601192481/50000000000000000000)
  directionLo := (158798556691317774421/50000000000000000000)
  directionHi := (317597113382635548843/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree129.table
  base := (-2474401287300981546538013208583878878773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (12257)
      previous := (4403)
      next := (0)
      square := (186756060285130828790833845800000000000000)
      linear := (-12480722677447578216614054732020000000000000)
      constant := (206007734912555470278955372604372298698802460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree129.table
  base := (-154650082461801789253842120475326857219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6069)
      previous := (2261)
      next := (0)
      square := (93378030142565414395416922900000000000000)
      linear := (-6412443708557945371978581409640000000000000)
      constant := (108833195480195203455091346021504437439403040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell002.Kernel129
