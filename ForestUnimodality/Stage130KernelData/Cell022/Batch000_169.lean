import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell022.Parameters
import ForestUnimodality.BinomialMassData.Q64_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q64_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q64_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q64_153.Batch150_199
import ForestUnimodality.BinomialMassData.Q65_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q65_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q65_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q65_153.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree000.table
  base := (279309991821729776975580253/12500000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4717)
      previous := (3392)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (207969789819372863626245611700000000000000)
      constant := (34187542998979724701811022967200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree000.table
  base := (279309991821729776975580253/12500000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4664)
      previous := (3445)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (207969789819372863626245611700000000000000)
      constant := (34187542998979724701811022967200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree001.table
  base := (35250163501224282025509898569893346576103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (24843056408649609190508743711380000000000000)
      constant := (3288833342959901989162799252597413399999980508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree001.table
  base := (34929693666263173025761918304893346576103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (24734051386247821082003949416400000000000000)
      constant := (3258663812801343399181768246055743399999980508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24664002959625108003/50000000000000000000)
  directionHi := (49328005919250216007/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree002.table
  base := (91490531919116237987406737404334242812593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (17866734974935170246201908832660000000000000)
      constant := (2120918128228532211279981314623180289999989537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree002.table
  base := (8996428189743684297951278469432552308941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (17648724930131594029192320242700000000000000)
      constant := (2084958014282117248544927761065466169999998690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24664002959625108003/50000000000000000000)
  centralHi := (49328005919250216007/100000000000000000000)
  directionLo := (17440083743955991781/25000000000000000000)
  directionHi := (558082679806591737/800000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree003.table
  base := (3067497764906378913208610848204741731033/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (1210045949024525700210563772660000000000000)
      constant := (156593644788654857335319472529690664848336660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree003.table
  base := (59969422336023865396317686309333411089439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (1173710941557262997375632341000000000000000)
      constant := (152979508388629161061151542256326202243630839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/25000000000000000000)
  centralHi := (558082679806591737/800000000000000000)
  directionLo := (21359653122049923993/25000000000000000000)
  directionHi := (85438612488199695973/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree004.table
  base := (5329467056461845110093050008462454439147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (3914092107506292357588239075220000000000000)
      constant := (968165286927242895476772532680460767727936984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree004.table
  base := (20752898718410340078024455502449635865427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (3478072017899139923569061895300000000000000)
      constant := (941617914931645011265824753379687051947561286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/25000000000000000000)
  centralHi := (85438612488199695973/100000000000000000000)
  directionLo := (98656011838500432013/100000000000000000000)
  directionHi := (49328005919250216007/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree005.table
  base := (30696517328750347356547981236404332592109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-3062229326208146586718595803500000000000000)
      constant := (688501939099142082264885828410989021648679581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree005.table
  base := (29808570764889050915667471746328799656993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-3607254438217087129242567278400000000000000)
      constant := (667824976478595759137110732788560871170549137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98656011838500432013/100000000000000000000)
  centralHi := (49328005919250216007/50000000000000000000)
  directionLo := (55150387214977742483/50000000000000000000)
  directionHi := (110300774429955484967/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree006.table
  base := (5704355624024295820004181729449756443649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-1115394528880287281225047853580000000000000)
      constant := (56311137844208787640206797636715266039724196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree006.table
  base := (2765860197834263791449243259126906620271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-1188064543814812686894910716900000000000000)
      constant := (54560206792565867057596790905912672954598968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/50000000000000000000)
  centralHi := (110300774429955484967/100000000000000000000)
  directionLo := (120828444531151298303/100000000000000000000)
  directionHi := (471986111449809759/390625000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree007.table
  base := (17403415726097784430308831996585954699687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-17014872193637024475332265560940000000000000)
      constant := (385721988370688046842012767694800613564972983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree007.table
  base := (8430957393800343225327566217297686484261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-17777907350449541234865825625800000000000000)
      constant := (373841906158953944157774434381193085820131498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120828444531151298303/100000000000000000000)
  centralHi := (471986111449809759/390625000000000000)
  directionLo := (130509636333058144167/100000000000000000000)
  directionHi := (16313704541632268021/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree008.table
  base := (1351354998152729440415282500806003849243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-23991193627351463419639100439660000000000000)
      constant := (303240553223172292961158719786797441069293870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree008.table
  base := (13080292577981331234393746559855567924267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-24863233806565768287677454799500000000000000)
      constant := (294375670596477709923074113967658989539166203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130509636333058144167/100000000000000000000)
  centralHi := (16313704541632268021/12500000000000000000)
  directionLo := (17440083743955991781/12500000000000000000)
  directionHi := (139520669951647934249/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree009.table
  base := (1058927687631796707325401476912230848201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-3440835006785100262660659479820000000000000)
      constant := (27364541776207995333560956566807124361708010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree009.table
  base := (2558351296804154225750805200410425641691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-3549840029186888371165453774800000000000000)
      constant := (26644527602148677324086468317820068376153164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/12500000000000000000)
  centralHi := (139520669951647934249/100000000000000000000)
  directionLo := (7399200887887532401/5000000000000000000)
  directionHi := (147984017757750648021/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree010.table
  base := (8296025948581180755662450248441549740259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-37943836494780341308252770197100000000000000)
      constant := (207010996716436297011916031945768237869722931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree010.table
  base := (1599116058182709375479769987658170242609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-39033886718798222393300713146900000000000000)
      constant := (202493476185819445219092872525450536046170405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7399200887887532401/5000000000000000000)
  centralHi := (147984017757750648021/100000000000000000000)
  directionLo := (77994425569549269357/50000000000000000000)
  directionHi := (31197770227819707743/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree011.table
  base := (1286159249127390110878541257866483047633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-44920157928494780252559605075820000000000000)
      constant := (180678866113579543537229170827462508310204485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree011.table
  base := (6170732083001736902873742646243757269379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-46119213174914449446112342320600000000000000)
      constant := (177863681261620132811584467969670113918893011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77994425569549269357/50000000000000000000)
  centralHi := (31197770227819707743/20000000000000000000)
  directionLo := (81801243645291585241/50000000000000000000)
  directionHi := (163602487290583170483/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree012.table
  base := (4868209790917340253204751855651291158291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-5766275484689913244096271106060000000000000)
      constant := (18261056791535875410225015469029008302714891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree012.table
  base := (2319231669550652388726661761887963178107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-5911615514558964055435996832700000000000000)
      constant := (18121442780136832914247796179341184452512614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81801243645291585241/50000000000000000000)
  centralHi := (163602487290583170483/100000000000000000000)
  directionLo := (21359653122049923993/12500000000000000000)
  directionHi := (34175444995279878389/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree013.table
  base := (1764488643163343893623976675456923792443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-58872800795923658141173274833260000000000000)
      constant := (156166848568044949200215455267062258114596374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree013.table
  base := (1661450431577761775049724063290043409967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-60289866087146903551735600668000000000000000)
      constant := (156405271818161614272178042161863252367835006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/12500000000000000000)
  centralHi := (34175444995279878389/20000000000000000000)
  directionLo := (35570930931649565993/20000000000000000000)
  directionHi := (88927327329123914983/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree014.table
  base := (2361428020551517514630046980441284542733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-65849122229638097085480109711980000000000000)
      constant := (154921318765108603760744115795230029860836797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree014.table
  base := (434927047369216211392376427811825665021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-67375192543263130604547229841700000000000000)
      constant := (156643916578997117499857962519235134962382945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35570930931649565993/20000000000000000000)
  centralHi := (88927327329123914983/50000000000000000000)
  directionLo := (184568497722591275553/100000000000000000000)
  directionHi := (92284248861295637777/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree015.table
  base := (1330659281223897473567000726112542125351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-8091715962594726225531882732300000000000000)
      constant := (17755098235688102564467635032618722068037951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree015.table
  base := (290054802935214219239811660443632796237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-8273390999931039739706539890600000000000000)
      constant := (18113994740576722108241769729005555612049748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184568497722591275553/100000000000000000000)
  centralHi := (92284248861295637777/50000000000000000000)
  directionLo := (191046545426876968741/100000000000000000000)
  directionHi := (95523272713438484371/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree016.table
  base := (412133678959000724125671069074467857139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-79801765097066974974093779469420000000000000)
      constant := (170216148888188493321714297129244218067766851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree016.table
  base := (256030390890963482124190272110469572673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-81545845455495584710170488189100000000000000)
      constant := (174998403386565250552944209239833982226702257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191046545426876968741/100000000000000000000)
  centralHi := (95523272713438484371/50000000000000000000)
  directionLo := (197312023677000864027/100000000000000000000)
  directionHi := (49328005919250216007/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree017.table
  base := (-51515440292743133256036043383024845711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-5104593325340083171670624373420000000000000)
      constant := (10927137792279950173951645143852598299647624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree017.table
  base := (-138835568159874011720903453546221005003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-5213598347741871280175418668400000000000000)
      constant := (11303158443846997720666182144617414704443476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197312023677000864027/100000000000000000000)
  centralHi := (49328005919250216007/25000000000000000000)
  directionLo := (101692289353080912329/50000000000000000000)
  directionHi := (203384578706161824659/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree018.table
  base := (-72237759180404357857663382083537133427/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-10417156440499539206967494358540000000000000)
      constant := (22901216994447870691663975598091518655301968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree018.table
  base := (-643624521498922608200698079399179226857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-10635166485303115423977082948500000000000000)
      constant := (23797700756474103901052262162965469661889886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101692289353080912329/50000000000000000000)
  centralHi := (203384578706161824659/100000000000000000000)
  directionLo := (52320251231867975343/25000000000000000000)
  directionHi := (209281004927471901373/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree019.table
  base := (-1829702084495339165731918882623163885789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-100730729398210291807014284105580000000000000)
      constant := (231012306165189233918380288349954356597565299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree019.table
  base := (-975139485498354562167600585682037668243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-102801824823844265868605375710200000000000000)
      constant := (240827364084696431210497404679288360448199226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52320251231867975343/25000000000000000000)
  centralHi := (209281004927471901373/100000000000000000000)
  directionLo := (21501579288838785809/10000000000000000000)
  directionHi := (215015792888387858091/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree020.table
  base := (-2442570192110148976323512111610667315451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-107707050831924730751321118984300000000000000)
      constant := (260260506486088534865292224275305888812607541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree020.table
  base := (-2553061819060552943875656069516917378927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-109887151279960492921417004883900000000000000)
      constant := (271895851266093144315186839558678481076697857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21501579288838785809/10000000000000000000)
  centralHi := (215015792888387858091/100000000000000000000)
  directionLo := (55150387214977742483/25000000000000000000)
  directionHi := (220601548859910969933/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree021.table
  base := (-1500831734160618233289499989641757164401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-12742596918404352188403105984780000000000000)
      constant := (32631746850080836999713363235003579230785998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree021.table
  base := (-3102776712557239130986985931875282553281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-12996941970675191108247626006400000000000000)
      constant := (34135190245191198021319124359942390078916119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/25000000000000000000)
  centralHi := (220601548859910969933/100000000000000000000)
  directionLo := (2825616512577423101/1250000000000000000)
  directionHi := (226049321006193848081/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree022.table
  base := (-1756547030343182032719622579179035553941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-121659693699353608639934788741740000000000000)
      constant := (331144872396926567615687768563515913435590262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree022.table
  base := (-360548601214162688789033942434246645757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-124057804192192947027040263231300000000000000)
      constant := (346648033106009745775758374601567202694743870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2825616512577423101/1250000000000000000)
  centralHi := (226049321006193848081/100000000000000000000)
  directionLo := (57842214091078658141/25000000000000000000)
  directionHi := (46273771272862926513/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree023.table
  base := (-995517970997764247367111643124335040831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-128636015133068047584241623620460000000000000)
      constant := (372515999829471278925543390016729764116748484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree023.table
  base := (-63536927577263481538481963668473042739/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-131143130648309174079851892405000000000000000)
      constant := (390068704058267024216685889890771730721455936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57842214091078658141/25000000000000000000)
  centralHi := (46273771272862926513/20000000000000000000)
  directionLo := (236568805769696609849/100000000000000000000)
  directionHi := (4731376115393932197/2000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree024.table
  base := (-2206537200253055462880200036830298549251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-15068037396309165169838717611020000000000000)
      constant := (46410476781562734520867607375128786946796298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree024.table
  base := (-179594251427724718511260910509149589261/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-15358717456047266792518169064300000000000000)
      constant := (48597179243474186626387972098142547958303475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236568805769696609849/100000000000000000000)
  centralHi := (4731376115393932197/2000000000000000000)
  directionLo := (241656889062302596607/100000000000000000000)
  directionHi := (471986111449809759/195312500000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree025.table
  base := (-4809971443541268354842765623780970067657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-142588658000496925472855293377900000000000000)
      constant := (466589157082758801175811005592911271686217287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree025.table
  base := (-4879807070710502515429639047445408542611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-145313783560541628185475150752400000000000000)
      constant := (488475816190360616493176222557100431426019101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241656889062302596607/100000000000000000000)
  centralHi := (471986111449809759/195312500000000000)
  directionLo := (123320014798125540017/50000000000000000000)
  directionHi := (49328005919250216007/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree026.table
  base := (-2588060307258176963954259386156060179319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-149564979434211364417162128256620000000000000)
      constant := (519121999883917175129774643029825574524643058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree026.table
  base := (-261977312525010342419547271012525810119/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-152399110016657855238286779926100000000000000)
      constant := (543294348666996651365971686297355666218486580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123320014798125540017/50000000000000000000)
  centralHi := (49328005919250216007/20000000000000000000)
  directionLo := (251524464748877247353/100000000000000000000)
  directionHi := (125762232374438623677/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree027.table
  base := (-2757221350418517926362528875754813105489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-17393477874213978151274329237260000000000000)
      constant := (63913827413906716163785817052003462225246222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree027.table
  base := (-5571967199037463297959424416184821149901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-17720492941419342476788712122200000000000000)
      constant := (66862497736643285610619144771253280189107499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251524464748877247353/100000000000000000000)
  centralHi := (125762232374438623677/50000000000000000000)
  directionLo := (64078959366149771979/25000000000000000000)
  directionHi := (256315837464599087917/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree028.table
  base := (-1456870742604042203169861934533570426577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-163517622301640242305775798014060000000000000)
      constant := (634836915429916596925296328184734599537036028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree028.table
  base := (-2939793623052354364056628730557392847939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-166569762928890309343910038273500000000000000)
      constant := (663821280905862309333112823490763981645191898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64078959366149771979/25000000000000000000)
  centralHi := (256315837464599087917/100000000000000000000)
  directionLo := (52203854533223257667/20000000000000000000)
  directionHi := (16313704541632268021/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree029.table
  base := (-764682757963952795243599185336288651027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-170493943735354681250082632892780000000000000)
      constant := (697907423025707361089714722075382551744871656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree029.table
  base := (-6164598707019481954496904256863366207813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-173655089385006536396721667447200000000000000)
      constant := (729419432585946601743172090785835460441305483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52203854533223257667/20000000000000000000)
  centralHi := (16313704541632268021/6250000000000000000)
  directionLo := (265639441482468762717/100000000000000000000)
  directionHi := (132819720741234381359/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree030.table
  base := (-6386318922449812478452685906941722905711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-19718918352118791132709940863500000000000000)
      constant := (84932286758406562926689759028044578722245689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree030.table
  base := (-6428912089392904126944097498202277056141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-20082268426791418161059255180100000000000000)
      constant := (88723579066374856969921361797175877376977259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265639441482468762717/100000000000000000000)
  centralHi := (132819720741234381359/50000000000000000000)
  directionLo := (270180615587217008689/100000000000000000000)
  directionHi := (27018061558721700869/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree031.table
  base := (-3317873706997826770712276111710052411477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-184446586602783559138696302650220000000000000)
      constant := (834246737088626431973300358097638766199469814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree031.table
  base := (-6674193034578622366079934827410177889293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-187825742297238990502344925794600000000000000)
      constant := (871060626941696116844760408948905145789540163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270180615587217008689/100000000000000000000)
  centralHi := (27018061558721700869/10000000000000000000)
  directionLo := (274646713446669728731/100000000000000000000)
  directionHi := (68661678361667432183/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree032.table
  base := (-6867227826269082236588940565219014271581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-191422908036497998083003137528940000000000000)
      constant := (907441239754691660112866355363508094916560371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree032.table
  base := (-6901894114780433739771596221413334002171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-194911068753355217555156554968300000000000000)
      constant := (947030675356195128527873733028935264343179061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274646713446669728731/100000000000000000000)
  centralHi := (68661678361667432183/25000000000000000000)
  directionLo := (17440083743955991781/6250000000000000000)
  directionHi := (279041339903295868497/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree033.table
  base := (-7082054100151667804466888931277035028807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-22044358830023604114145552489740000000000000)
      constant := (109327088773528677378616538281428431890072993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree033.table
  base := (-7113282326910403029320245067816913347133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-22444043912163493845329798238000000000000000)
      constant := (114043633078906247034794810519358208384107067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/6250000000000000000)
  centralHi := (279041339903295868497/100000000000000000000)
  directionLo := (141683910115965782059/50000000000000000000)
  directionHi := (283367820231931564119/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree034.table
  base := (-3640678732071218913249459103541942726663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-12080914759054522115977459252140000000000000)
      constant := (62572231398934823776670980717485489730770098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree034.table
  base := (-365473146914118968247158010298960582167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-12298924803858098332987047842100000000000000)
      constant := (65242401223589970994784871384366625567120820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141683910115965782059/50000000000000000000)
  centralHi := (283367820231931564119/100000000000000000000)
  directionLo := (71907307395948061179/25000000000000000000)
  directionHi := (287629229583792244717/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree035.table
  base := (-7466126998268670833492530454166352386133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-212351872337641314915923642165100000000000000)
      constant := (1146770490840734820372767022598419856993012603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree035.table
  base := (-93642502630086154582465278875649825483/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-216167048121703898713591442489400000000000000)
      constant := (1195192472231114991448871669907743058821476240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71907307395948061179/25000000000000000000)
  centralHi := (287629229583792244717/100000000000000000000)
  directionLo := (145914209279747197087/50000000000000000000)
  directionHi := (11673136742379775767/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree036.table
  base := (-7637227556516673013121196977843203396503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-24369799307928417095581164115980000000000000)
      constant := (137005691641257900374264622883349827965695697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree036.table
  base := (-957491929251576859489341366906283864579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-24805819397535569529600341295900000000000000)
      constant := (142731995358416130486218818167414045345840168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145914209279747197087/50000000000000000000)
  centralHi := (11673136742379775767/4000000000000000000)
  directionLo := (295968035515501296041/100000000000000000000)
  directionHi := (147984017757750648021/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree037.table
  base := (-155908308095888381832959271058730761559/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-226304515205070192804537311922540000000000000)
      constant := (1322552432145011072823158783709628580133268450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree037.table
  base := (-781580263822810407838931299862296930489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-230337701033936352819214700836800000000000000)
      constant := (1377290095897049660537415581829984911541829990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295968035515501296041/100000000000000000000)
  centralHi := (147984017757750648021/50000000000000000000)
  directionLo := (60010109219988800441/20000000000000000000)
  directionHi := (150025273049972001103/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree038.table
  base := (-49633449224650360946589106923955789183/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-233280836638784631748844146801260000000000000)
      constant := (1415258631821302870231231732910259028962424480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree038.table
  base := (-19899105704959481696723382456393146459/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-237423027490052579872026330010500000000000000)
      constant := (1473283892741925950749628112529317133816507600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60010109219988800441/20000000000000000000)
  centralHi := (150025273049972001103/50000000000000000000)
  directionLo := (38009781303395323621/12500000000000000000)
  directionHi := (304078250427162588969/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree039.table
  base := (-4037807649633537659054067042361490408763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-26695239785833230077016775742220000000000000)
      constant := (167906253965508666910819757810755526893614874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree039.table
  base := (-809201319147849217614467723972485512803/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-27167594882907645213870884353800000000000000)
      constant := (174728474133098451847199450057225651811993970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38009781303395323621/12500000000000000000)
  centralHi := (304078250427162588969/100000000000000000000)
  directionLo := (3850666227883774221/1250000000000000000)
  directionHi := (308053298230701937681/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree040.table
  base := (-4099355713050509627083271125130290531193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-247233479506213509637457816558700000000000000)
      constant := (1610233554616775820170601455599650057910606126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree040.table
  base := (-8213402971081316639221784506659849765851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-251593680402285033977649588357900000000000000)
      constant := (1675095804934253416934184126863599576831193941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3850666227883774221/1250000000000000000)
  centralHi := (308053298230701937681/100000000000000000000)
  directionLo := (77994425569549269357/25000000000000000000)
  directionHi := (311977702278197077429/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree041.table
  base := (-8311082543084691227522002333317586629093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-254209800939927948581764651437420000000000000)
      constant := (1712480085114968615907206621076648614599561963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree041.table
  base := (-8324237084426502300307479828868141387583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-258679006858401261030461217531600000000000000)
      constant := (1780892546272814165713852622264775678258069553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77994425569549269357/25000000000000000000)
  centralHi := (311977702278197077429/100000000000000000000)
  directionLo := (6317067005715641711/2000000000000000000)
  directionHi := (315853350285782085551/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree042.table
  base := (-1682623087895887074960500264508291627627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-29020680263738043058452387368460000000000000)
      constant := (201987424759370842723652085478949667382710865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree042.table
  base := (-8424886776443154511382846566798510671277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-29529370368279720898141427411700000000000000)
      constant := (209993088971224765086586150703757073744008523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6317067005715641711/2000000000000000000)
  centralHi := (315853350285782085551/100000000000000000000)
  directionLo := (39960251941523588551/12500000000000000000)
  directionHi := (319682015532188708409/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree043.table
  base := (-8505148373327720469880215176176794527039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-268162443807356826470378321194860000000000000)
      constant := (1926445849492366574460014133294797416916544049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree043.table
  base := (-4257837992381153439758827870605396634917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-272849659770633715136084475879000000000000000)
      constant := (2002223985282874711422556059245746540346455894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39960251941523588551/12500000000000000000)
  centralHi := (319682015532188708409/100000000000000000000)
  directionLo := (64693073268377697921/20000000000000000000)
  directionHi := (161732683170944244803/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree044.table
  base := (-1073434645331270586460959213865228966593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-275138765241071265414685156073580000000000000)
      constant := (2038150240285010934798011122550310840968195704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree044.table
  base := (-8596887369715970093069241074764000784687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-279934986226749942188896105052700000000000000)
      constant := (2117744483102657604439937905886849505631262017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64693073268377697921/20000000000000000000)
  centralHi := (161732683170944244803/50000000000000000000)
  directionLo := (81801243645291585241/25000000000000000000)
  directionHi := (65440994916233268193/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree045.table
  base := (-1732072102361315067813323173856736861221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-31346120741642856039887998994700000000000000)
      constant := (239221548800212437385363718907993137119820895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree045.table
  base := (-8668767575497683177593690309288169223187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-31891145853651796582411970469600000000000000)
      constant := (248499280056271667753575382034291471850490613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81801243645291585241/25000000000000000000)
  centralHi := (65440994916233268193/20000000000000000000)
  directionLo := (165451161644933227449/50000000000000000000)
  directionHi := (330902323289866454899/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree046.table
  base := (-2181006167297180361801840988672894777503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-289091408108500143303298825831020000000000000)
      constant := (2270971649994466658126030921358704824613729092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree046.table
  base := (-8731531820606065377425209806615288383207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-294105639138982396294519363400100000000000000)
      constant := (2358466059444402749558658219786942714237507337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165451161644933227449/50000000000000000000)
  centralHi := (330902323289866454899/100000000000000000000)
  directionLo := (41819851694238930551/12500000000000000000)
  directionHi := (334558813553911444409/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree047.table
  base := (-8778667500264548127216559592037546222773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-296067729542214582247605660709740000000000000)
      constant := (2392078740829935972665388102313513080471106843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree047.table
  base := (-4392683951564831502594190587244252357593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-301190965595098623347330992573800000000000000)
      constant := (2483657703751076043137148419466148593122210926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41819851694238930551/12500000000000000000)
  centralHi := (334558813553911444409/100000000000000000000)
  directionLo := (338175770708917678887/100000000000000000000)
  directionHi := (42271971338614709861/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree048.table
  base := (-1103057756175472662106196854032549999209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-33671561219547669021323610620940000000000000)
      constant := (279590128990296551786401056521770699616459128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree048.table
  base := (-1766087939098843714304187981934093610447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-34252921339023872266682513527500000000000000)
      constant := (290229401926316742676236698566947112596136765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338175770708917678887/100000000000000000000)
  centralHi := (42271971338614709861/12500000000000000000)
  directionLo := (21359653122049923993/6250000000000000000)
  directionHi := (341754449952798783889/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree049.table
  base := (-1107694956834199569468056106628429788413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-310020372409643460136219330467180000000000000)
      constant := (2643665367569851124750768281395960696664320664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree049.table
  base := (-354675607750578908178060378335439105747/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-315361618507331077452954250921200000000000000)
      constant := (2743683452806847159044081776443392649339211925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/6250000000000000000)
  centralHi := (341754449952798783889/100000000000000000000)
  directionLo := (21581002589671969503/6250000000000000000)
  directionHi := (345296041434751512049/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree050.table
  base := (-4445046335861380057377650427068133031689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-316996693843357899080526165345900000000000000)
      constant := (2774138262488100480454980344065524147722384398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree050.table
  base := (-1778968835657233653965571286747410381319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-322446944963447304505765880094900000000000000)
      constant := (2878511289177951973264372518842649351918517645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21581002589671969503/6250000000000000000)
  centralHi := (345296041434751512049/100000000000000000000)
  directionLo := (17440083743955991781/5000000000000000000)
  directionHi := (348801674879119835621/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree051.table
  base := (-1782035371164330908391689476575244747493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4717)
      previous := (3392)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-2117470688085440117809366014540000000000000)
      constant := (19004752522564004233033641847379937768167855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree051.table
  base := (-4457205267605373159774874179567575807237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4664)
      previous := (3445)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-2153805695552702820644297446200000000000000)
      constant := (19715984166890497014137783374802321802985478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/5000000000000000000)
  centralHi := (348801674879119835621/100000000000000000000)
  directionLo := (352272423795063472951/100000000000000000000)
  directionHi := (44034052974382934119/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree052.table
  base := (-1784382688992638939023741996643510912047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-330949336710786776969139835103340000000000000)
      constant := (3044429618082251482442852149623980265299458885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree052.table
  base := (-4462842141063896283337688328228776369739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-336617597875679758611389138442300000000000000)
      constant := (3157784093608974756783227585954985147921559498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352272423795063472951/100000000000000000000)
  centralHi := (44034052974382934119/12500000000000000000)
  directionLo := (35570930931649565993/10000000000000000000)
  directionHi := (355709309316495659931/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree053.table
  base := (-1785078196308541072889517427382879906647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-337925658144501215913446669982060000000000000)
      constant := (3184243636189044826807034217030690821326501885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree053.table
  base := (-4464374167759741659099114251059000902391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-343702924331795985664200767616000000000000000)
      constant := (3302224896410206848954402166360669695751858162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35570930931649565993/10000000000000000000)
  centralHi := (355709309316495659931/100000000000000000000)
  directionLo := (179556651855610719977/50000000000000000000)
  directionHi := (71822660742244287991/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree054.table
  base := (-8920686905425130860380754302146405375679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-38322442175357294984194833873420000000000000)
      constant := (369685264164763799931522742007637199617858921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree054.table
  base := (-4461837526471819190784296552087385105817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-38976472309768023635223599643300000000000000)
      constant := (383318476902207923978222308610041422679539966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179556651855610719977/50000000000000000000)
  centralHi := (71822660742244287991/20000000000000000000)
  directionLo := (362485333593453894911/100000000000000000000)
  directionHi := (1415958334349429277/390625000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree055.table
  base := (-4453934473544979326305251957497518970613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-351878301011930093802060339739500000000000000)
      constant := (3473199256460945277994836659101881156833840566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree055.table
  base := (-4455263789328764595910895859940268366371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-357873577244028439769824025963400000000000000)
      constant := (3600706802594049690309281584033066515623242522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362485333593453894911/100000000000000000000)
  centralHi := (1415958334349429277/390625000000000000)
  directionLo := (2926610262958314869/800000000000000000)
  directionHi := (182913141434894679313/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree056.table
  base := (-8886996345943404333672541485149164861557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-358854622445644532746367174618220000000000000)
      constant := (3622337886387997961834761829853823199755812187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree056.table
  base := (-8889361017734956573987297319040743819893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-364958903700144666822635655137100000000000000)
      constant := (3754745137878069368957129653238575227920124763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2926610262958314869/800000000000000000)
  centralHi := (182913141434894679313/50000000000000000000)
  directionLo := (369136995445182551107/100000000000000000000)
  directionHi := (92284248861295637777/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree057.table
  base := (-8858120915738651861035666679346999020189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-40647882653262107965630445499660000000000000)
      constant := (419398006039542663071454784325098455548488411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree057.table
  base := (-4430111730268012770991379700601483488601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-41338247795140099319494142701200000000000000)
      constant := (434664463580521183719638525330221082892297598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369136995445182551107/100000000000000000000)
  centralHi := (92284248861295637777/25000000000000000000)
  directionLo := (186209138856197326429/50000000000000000000)
  directionHi := (372418277712394652859/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree058.table
  base := (-8821287976291441113722833933359164733141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-372807265313073410634980844375660000000000000)
      constant := (3929930699473036640591782005931115312761902331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree058.table
  base := (-8823156876602979727647368710616803188387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-379129556612377120928258913484500000000000000)
      constant := (4072410923168899162690409192101171254163048717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186209138856197326429/50000000000000000000)
  centralHi := (372418277712394652859/100000000000000000000)
  directionLo := (375670900845721469859/100000000000000000000)
  directionHi := (18783545042286073493/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree059.table
  base := (-8776537168270389297733662360825808369269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-379783586746787849579287679254380000000000000)
      constant := (4088382893791044320505583587038308651883781979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree059.table
  base := (-8778197894624506478475013700267666831497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-386214883068493347981070542658200000000000000)
      constant := (4236036533269721414480632610830184187141486727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375670900845721469859/100000000000000000000)
  centralHi := (18783545042286073493/5000000000000000000)
  directionLo := (189447801458743165673/50000000000000000000)
  directionHi := (378895602917486331347/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree060.table
  base := (-8723903165735724707213798091572844699751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-42973323131166920947066057125900000000000000)
      constant := (472215313958314569249649152443819030935947649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree060.table
  base := (-4362689241494904269940112068394903136429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-43700023280512175003764685759100000000000000)
      constant := (489206250464348284642223139650209713884296342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189447801458743165673/50000000000000000000)
  centralHi := (378895602917486331347/100000000000000000000)
  directionLo := (382093090853753937483/100000000000000000000)
  directionHi := (95523272713438484371/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree061.table
  base := (-2165854074814665512807581564309757215833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-393736229614216727467901349011820000000000000)
      constant := (4414594784966055483691006964952771573338261212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree061.table
  base := (-541545408975185141432816797685653990151/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-400385535980725802086693801005600000000000000)
      constant := (4572869432741466081286524162966374411912883856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382093090853753937483/100000000000000000000)
  centralHi := (95523272713438484371/25000000000000000000)
  directionLo := (385264042243945529131/100000000000000000000)
  directionHi := (96316010560986382283/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree062.table
  base := (-859510310084328804656902283401603597313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-400712551047931166412208183890540000000000000)
      constant := (4582353150727033735884839136086838613904999830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree062.table
  base := (-268633325937912092428761915747042141943/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-407470862436842029139505430179300000000000000)
      constant := (4746075498864482298169795822502879695976202016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385264042243945529131/100000000000000000000)
  centralHi := (96316010560986382283/25000000000000000000)
  directionLo := (388409107017477423063/100000000000000000000)
  directionHi := (48551138377184677883/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree063.table
  base := (-8518986780464551132198664356256464731953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-45298763609071733928501668752140000000000000)
      constant := (528134708842829145757835421722656935232190247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree063.table
  base := (-2130004849876892781806401985960547026663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-46061798765884250688035228817000000000000000)
      constant := (546941550548483306407116173303816468734598148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388409107017477423063/100000000000000000000)
  centralHi := (48551138377184677883/12500000000000000000)
  directionLo := (391528908999174432503/100000000000000000000)
  directionHi := (48941113624896804063/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree064.table
  base := (-8435087642804398769111968564983684555671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-414665193915360044300821853647980000000000000)
      constant := (4927171996229041503383667413604376928236297561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree064.table
  base := (-8436004007583307584347936698308660543409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-421641515349074483245128688526700000000000000)
      constant := (5102064366591434673211929010405292565339338719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391528908999174432503/100000000000000000000)
  centralHi := (48941113624896804063/12500000000000000000)
  directionLo := (78924809470800345611/20000000000000000000)
  directionHi := (49328005919250216007/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree065.table
  base := (-8343423451691102393651360041832830154213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-421641515349074483245128688526700000000000000)
      constant := (5104231584824315304520945173356735278920027883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree065.table
  base := (-65189347282372604099727672060581112733/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-428726841805190710297940317700400000000000000)
      constant := (5284846354653018765441625152264683661700249984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78924809470800345611/20000000000000000000)
  centralHi := (49328005919250216007/12500000000000000000)
  directionLo := (397695097930591775371/100000000000000000000)
  directionHi := (99423774482647943843/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree066.table
  base := (-515250609300309989744044299367952572773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-47624204086976546909937280378380000000000000)
      constant := (587154531284009958147536125095423285731478832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree066.table
  base := (-8244730873826081147054679419580441335381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-48423574251256326372305771874900000000000000)
      constant := (607868843122546915854581592169671272086674019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397695097930591775371/100000000000000000000)
  centralHi := (99423774482647943843/25000000000000000000)
  directionLo := (8014852290241974683/2000000000000000000)
  directionHi := (400742614512098734151/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree067.table
  base := (-8136860132389907987100828009271125313039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-435594158216503361133742358284140000000000000)
      constant := (5467649268103072141117531982908892227547070049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree067.table
  base := (-1017187452256650405700909645244702894843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-442897494717423164403563576047800000000000000)
      constant := (5659983777947144367022263983975483999476961704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8014852290241974683/2000000000000000000)
  centralHi := (400742614512098734151/100000000000000000000)
  directionLo := (100941782495518843779/25000000000000000000)
  directionHi := (403767129982075375117/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree068.table
  base := (-4010993250495141563417697565079368613997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-26033557626483400004591129009580000000000000)
      constant := (332588633290131675877706501855531418837052262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree068.table
  base := (-8022553463686617959021451232954185748141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-26469577716090552438610306189500000000000000)
      constant := (344255215991959701134497732646222086224809843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100941782495518843779/25000000000000000000)
  centralHi := (403767129982075375117/100000000000000000000)
  directionLo := (101692289353080912329/25000000000000000000)
  directionHi := (406769157412323649317/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree069.table
  base := (-1974849816650515548655890116457123372767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-49949644564881359891372892004620000000000000)
      constant := (649273670145463871729016735342300088429732132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree069.table
  base := (-493743863908699551492781025283642841401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-50785349736628402056576314932800000000000000)
      constant := (671987116614478498146650528804545919512255984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101692289353080912329/25000000000000000000)
  centralHi := (406769157412323649317/100000000000000000000)
  directionLo := (204874595539503945597/50000000000000000000)
  directionHi := (81949838215801578239/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree070.table
  base := (-1553821508215412515412408324997331271333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-456523122517646677966662862920300000000000000)
      constant := (6036017850934542014835109680016687361346829015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree070.table
  base := (-155391058269219081304215860365674126191/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-464153474085771845561998463568900000000000000)
      constant := (6246619718553058795221082267324996718999744050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204874595539503945597/50000000000000000000)
  centralHi := (81949838215801578239/20000000000000000000)
  directionLo := (51588463426591151771/12500000000000000000)
  directionHi := (412707707412729214169/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree071.table
  base := (-1907779824784212792365586581380589957421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-463499443951361116910969697799020000000000000)
      constant := (6231671038128082838290540633183927078746927244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree071.table
  base := (-1907878478559800974921612207288151866299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-471238800541888072614810092742600000000000000)
      constant := (6448545510906748897399738882802116611847226836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51588463426591151771/12500000000000000000)
  centralHi := (412707707412729214169/100000000000000000000)
  directionLo := (51955645735966535439/12500000000000000000)
  directionHi := (415645165887732283513/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree072.table
  base := (-7485441520931840760259667640830769866009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-52275085042786172872808503630860000000000000)
      constant := (714491381054606255884773782547479167578510591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree072.table
  base := (-3742895547070359513043613993998320615309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-53147125222000477740846857990700000000000000)
      constant := (739295697759345646012686971407220736159162582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51955645735966535439/12500000000000000000)
  centralHi := (415645165887732283513/100000000000000000000)
  directionLo := (52320251231867975343/12500000000000000000)
  directionHi := (83712401970988760549/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree073.table
  base := (-1833020079178161725902463203330392448981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-477452086818789994799583367556460000000000000)
      constant := (6632271881989805749345145681149275372647215084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree073.table
  base := (-916548741195425764605875234218697689733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-485409453454120526720433351090000000000000000)
      constant := (6861966897138145948069409351804146046248321624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52320251231867975343/12500000000000000000)
  centralHi := (83712401970988760549/20000000000000000000)
  directionLo := (421458667323119192483/100000000000000000000)
  directionHi := (105364666830779798121/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree074.table
  base := (-896380129482325881784408001290749760341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-484428408252504433743890202435180000000000000)
      constant := (6837219270399510266958553411874758710881420248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree074.table
  base := (-3585657602475146378151558983789179544359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-492494779910236753773244980263700000000000000)
      constant := (7073462250819827466543665743032958192092200338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421458667323119192483/100000000000000000000)
  centralHi := (105364666830779798121/25000000000000000000)
  directionLo := (424335551691994388499/100000000000000000000)
  directionHi := (848671103383988777/200000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree075.table
  base := (-3501164181113311997366825833393377380139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-54600525520690985854244115257100000000000000)
      constant := (782807165008462624285351730574687650868516922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree075.table
  base := (-7002571100844320012963436381681901961521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-55508900707372553425117401048600000000000000)
      constant := (809794138112980629118250157664995372998083879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424335551691994388499/100000000000000000000)
  centralHi := (848671103383988777/200000000000000000)
  directionLo := (21359653122049923993/5000000000000000000)
  directionHi := (427193062440998479861/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree076.table
  base := (-3412973198768556838209643365472686730977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-498381051119933311632503872192620000000000000)
      constant := (7256407430002592587166857322414179752629118814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree076.table
  base := (-1706540317680741698123553253608063554787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-506665432822469207878868238611100000000000000)
      constant := (7506021788204886230928424995335155360983964468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/5000000000000000000)
  centralHi := (427193062440998479861/100000000000000000000)
  directionLo := (21501579288838785809/5000000000000000000)
  directionHi := (430031585776775716181/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree077.table
  base := (-6641898734298376396399038502933486347997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-505357372553647750576810707071340000000000000)
      constant := (7470648021081770371100590310153950018079738227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree077.table
  base := (-25945659797042259764940744682226316197/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-513750759278585434931679867784800000000000000)
      constant := (7727085811628383965392194550754593626020973312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21501579288838785809/5000000000000000000)
  centralHi := (430031585776775716181/100000000000000000000)
  directionLo := (432851495242488442519/100000000000000000000)
  directionHi := (10821287381062211063/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree078.table
  base := (-6450188519582289402084119570116239122593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-56925965998595798835679726883340000000000000)
      constant := (854220687182654599542746162548207662042135607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree078.table
  base := (-12900713609483807342584262375032239403/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-57870676192744629109387944106500000000000000)
      constant := (883482138658982395049827883603270572656398500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432851495242488442519/100000000000000000000)
  centralHi := (10821287381062211063/2500000000000000000)
  directionLo := (54456644036452805673/12500000000000000000)
  directionHi := (87130630458324489077/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree079.table
  base := (-6250818510799445152338138110182300455827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-519310015421076628465424376828780000000000000)
      constant := (7908421856140731102649694576922422528629545757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree079.table
  base := (-6250967402288568172923911761174797435079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-527921412190817889037303126132200000000000000)
      constant := (8178782039959926492719349498042409166842235689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54456644036452805673/12500000000000000000)
  centralHi := (87130630458324489077/20000000000000000000)
  directionLo := (438436906828790091403/100000000000000000000)
  directionHi := (109609226707197522851/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree080.table
  base := (-3021895562238882492531858689675103313337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-526286336854791067409731211707500000000000000)
      constant := (8131954979003787380796565144314791013076188334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree080.table
  base := (-755490354528359487445389418871457233133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-535006738646934116090114755305900000000000000)
      constant := (8409414137724687785490511735109104461036716824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438436906828790091403/100000000000000000000)
  centralHi := (109609226707197522851/25000000000000000000)
  directionLo := (55150387214977742483/12500000000000000000)
  directionHi := (88240619543964387973/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree081.table
  base := (-5829108478922607666610194267365478269637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-59251406476500611817115338509580000000000000)
      constant := (928731722627294454107095059762102391020674163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree081.table
  base := (-5829224975047433677375244988102963630511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-60232451678116704793658487164400000000000000)
      constant := (960359499720625424285358822574694191597040889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/12500000000000000000)
  centralHi := (88240619543964387973/20000000000000000000)
  directionLo := (221976026636625972031/50000000000000000000)
  directionHi := (443952053273251944063/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree082.table
  base := (-5606772431526196712307329099000236476221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-540238979722219945298344881464940000000000000)
      constant := (8588313386586624660881211398112223464328142611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree082.table
  base := (-2803437727053440810451157089416608923861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-549177391559166570195738013653300000000000000)
      constant := (8880246080960686003511188508063693203402675702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221976026636625972031/50000000000000000000)
  centralHi := (443952053273251944063/100000000000000000000)
  directionLo := (446684091695132922301/100000000000000000000)
  directionHi := (223342045847566461151/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree083.table
  base := (-5376784611397824757415476718998816970727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-547215301155934384242651716343660000000000000)
      constant := (8821138589690891671249823078514076693532251657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree083.table
  base := (-2688437852613550616266202424567280483017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-556262718015282797248549642827000000000000000)
      constant := (9120445854632340916229986439978359062346110094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446684091695132922301/100000000000000000000)
  centralHi := (223342045847566461151/50000000000000000000)
  directionLo := (89879904303793181303/20000000000000000000)
  directionHi := (112349880379741476629/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree084.table
  base := (-5139146447902021975557805323731075502959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-61576846954405424798550950135820000000000000)
      constant := (1006340119944272981248371759417295472616803641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree084.table
  base := (-5139226982524755498733603887116602066909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-62594227163488780477929030222300000000000000)
      constant := (1040426087682552954763821305883609718023969691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89879904303793181303/20000000000000000000)
  centralHi := (112349880379741476629/25000000000000000000)
  directionLo := (2825616512577423101/625000000000000000)
  directionHi := (452098642012387696161/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree085.table
  base := (-4893859195618180749786101270675834565021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-33009879060197838948897963888300000000000000)
      constant := (546828283920051243796642376470279375803966083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree085.table
  base := (-97878607699031807100723233470192770739/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-33554904172206779491421935363200000000000000)
      constant := (565318403456895977225857459754327227734619850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2825616512577423101/625000000000000000)
  centralHi := (452098642012387696161/100000000000000000000)
  directionLo := (454781743562134065543/100000000000000000000)
  directionHi := (56847717945266758193/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree086.table
  base := (-232046197808534157056291296292043326127/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-568144265457077701075572220979820000000000000)
      constant := (9538197805330209451506001749114471155573861140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree086.table
  base := (-4640986875964688279231857141576990938193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-577518697383631478406984530348100000000000000)
      constant := (9860180040951539132402913875542824219127840063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454781743562134065543/100000000000000000000)
  centralHi := (56847717945266758193/12500000000000000000)
  directionLo := (114362277009670089333/25000000000000000000)
  directionHi := (457449108038680357333/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree087.table
  base := (-4380341697322220388375535120695930820251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-63902287432310237779986561762060000000000000)
      constant := (1087045776990234990323950498739549883936527149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree087.table
  base := (-4380397300692432116475594502583063222843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-64956002648860856162199573280200000000000000)
      constant := (1123681812879143204171352419936531452557385357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114362277009670089333/25000000000000000000)
  centralHi := (457449108038680357333/100000000000000000000)
  directionLo := (460101009141855543341/100000000000000000000)
  directionHi := (230050504570927771671/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree088.table
  base := (-822422653934741920351911696673627289913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-582096908324506578964185890737260000000000000)
      constant := (10031723369474870660138337286354355293852132915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree088.table
  base := (-4112162400915315567239442885817363750963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-591689350295863932512607788695500000000000000)
      constant := (10369281666285141151222999861233901331953707133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460101009141855543341/100000000000000000000)
  centralHi := (230050504570927771671/50000000000000000000)
  directionLo := (462737712728629265129/100000000000000000000)
  directionHi := (46273771272862926513/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree089.table
  base := (-1918119710635557132619300112658345391997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-589073229758221017908492725615980000000000000)
      constant := (10283131917507468733978314017323641585437484454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree089.table
  base := (-3836282828140057921934687032422695908299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-598774676751980159565419417869200000000000000)
      constant := (10628616076818975281576160356452767111482628709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462737712728629265129/100000000000000000000)
  centralHi := (46273771272862926513/10000000000000000000)
  directionLo := (93071895424836601307/20000000000000000000)
  directionHi := (58169934640522875817/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree090.table
  base := (-888180202595446456911755976058450498549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-66227727910215050761422173388300000000000000)
      constant := (1170848624622280967152191229449087881013096204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree090.table
  base := (-888189788752496775131409637001315358967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-67317778134232931846470116338100000000000000)
      constant := (1210126614900975951702578743856638315005307332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93071895424836601307/20000000000000000000)
  centralHi := (58169934640522875817/12500000000000000000)
  directionLo := (233983276708647808071/50000000000000000000)
  directionHi := (467966553417295616143/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree091.table
  base := (-203847376041874041062323098005978043983/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-603025872625649895797106395373420000000000000)
      constant := (10795240468184689900357757561325728959494431248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree091.table
  base := (-3261591885263685898317344952134196251137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-612945329664212613671042676216600000000000000)
      constant := (11156852026362549517808849018619240599957133967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233983276708647808071/50000000000000000000)
  centralHi := (467966553417295616143/100000000000000000000)
  directionLo := (470559185740999190261/100000000000000000000)
  directionHi := (235279592870499595131/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree092.table
  base := (-2962751550972416270645304249383936881909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-610002194059364334741413230252140000000000000)
      constant := (11055940445301775882486630651212091421531392219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree092.table
  base := (-370347682803359355265633660624319459497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-620030656120328840723854305390300000000000000)
      constant := (11425753543197779547220862835673562446181077816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470559185740999190261/100000000000000000000)
  centralHi := (235279592870499595131/50000000000000000000)
  directionLo := (236568805769696609849/50000000000000000000)
  directionHi := (473137611539393219699/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree093.table
  base := (-531260372769882771935989019412079043863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-68553168388119863742857785014540000000000000)
      constant := (1257748615822735534565127692973425912034561685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree093.table
  base := (-2656328277398928023856656041185836886967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-69679553619605007530740659396000000000000000)
      constant := (1299760452829323356160197712677625638256998833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236568805769696609849/50000000000000000000)
  centralHi := (473137611539393219699/100000000000000000000)
  directionLo := (475702061821442334133/100000000000000000000)
  directionHi := (237851030910721167067/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree094.table
  base := (-2342209353065356679513335182752234338017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-623954836926793212630026900009580000000000000)
      constant := (11586631750181955332166368119908232946381360047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree094.table
  base := (-73194771096088957492789861160860443297/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-634201309032561294829477563737700000000000000)
      constant := (11973123615087294409468414653488733372251536864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475702061821442334133/100000000000000000000)
  centralHi := (237851030910721167067/50000000000000000000)
  directionLo := (956505522805050883/200000000000000000)
  directionHi := (478252761402525441501/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree095.table
  base := (-404094874026527768286789588428713025589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-630931158360507651574333734888300000000000000)
      constant := (11856623060405228811976135425998361283919935495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree095.table
  base := (-2020494960125565626040304124292532674099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-641286635488677521882289192911400000000000000)
      constant := (12251592154935890243379792352238186102632016509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (956505522805050883/200000000000000000)
  centralHi := (478252761402525441501/100000000000000000000)
  directionLo := (480789929134451102481/100000000000000000000)
  directionHi := (240394964567225551241/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree096.table
  base := (-67643889041465888108417698046989177389/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-70878608866024676724293396640780000000000000)
      constant := (1347745718421620369952627679413614528740280275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree096.table
  base := (-1691115402043807478685800470301260695143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-72041329104977083215011202453900000000000000)
      constant := (1392583298744571396251852510176746420931933057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480789929134451102481/100000000000000000000)
  centralHi := (240394964567225551241/50000000000000000000)
  directionLo := (96662755624921038643/20000000000000000000)
  directionHi := (471986111449809759/97656250000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree097.table
  base := (-677039098122233391470317867063856736057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-644883801227936529462947404645740000000000000)
      constant := (12405896959901609891735143887359324355331283374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree097.table
  base := (-84630889971814526217830387390119658199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-655457288400909975987912451258800000000000000)
      constant := (12818096210794867533797418550340105022739513744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96662755624921038643/20000000000000000000)
  centralHi := (471986111449809759/97656250000000000)
  directionLo := (485824515944851924417/100000000000000000000)
  directionHi := (242912257972425962209/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree098.table
  base := (-100941752508714190636185455808843497727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-651860122661650968407254239524460000000000000)
      constant := (12685179537006763081874548161618027825617086570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree098.table
  base := (-252357921108277759298555077243788866999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-662542614857026203040724080432500000000000000)
      constant := (13106131716259229247359853688735200585649681636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485824515944851924417/100000000000000000000)
  centralHi := (242912257972425962209/50000000000000000000)
  directionLo := (122080586207691942467/25000000000000000000)
  directionHi := (488322344830767769869/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree099.table
  base := (-164278857398512220884421482514676331607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-73204049343929489705729008267020000000000000)
      constant := (1440839910225511358881986547694637307445960772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree099.table
  base := (-657127924917942350883173477059178134871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-74403104590349158899281745511800000000000000)
      constant := (1488595133409793474757395001983919077671200529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122080586207691942467/25000000000000000000)
  centralHi := (488322344830767769869/100000000000000000000)
  directionLo := (245403730935874755723/50000000000000000000)
  directionHi := (490807461871749511447/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree100.table
  base := (-297172102848078443712212801870329838143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-665812765529079846295867909281900000000000000)
      constant := (13253035920450249946844261452441017448818910513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree100.table
  base := (-2321743192087212259399478614841026759/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-676713267769258657146347338779900000000000000)
      constant := (13691769660158638256113811569903463859788616832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245403730935874755723/50000000000000000000)
  centralHi := (490807461871749511447/100000000000000000000)
  directionLo := (493280059192502160069/100000000000000000000)
  directionHi := (49328005919250216007/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree101.table
  base := (35206141539147130509571947529810709023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-672789086962794285240174744160620000000000000)
      constant := (13541609718240661661758294022602330677775038814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree101.table
  base := (70402555053825388868875077156313076043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-683798594225374884199158967953600000000000000)
      constant := (13989372091170948262457490160639902132797090587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493280059192502160069/100000000000000000000)
  centralHi := (49328005919250216007/10000000000000000000)
  directionLo := (495740324126379716411/100000000000000000000)
  directionHi := (123935081031594929103/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree102.table
  base := (55704696819189090260096218786259602461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4717)
      previous := (3392)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-4442911165990253099244977640780000000000000)
      constant := (90413598573885465806344641058834381753412264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree102.table
  base := (55703624042774848273538521238186347959/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4664)
      previous := (3445)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-4515581180924778504914840504100000000000000)
      constant := (93399761376445478642206367151995540089901816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495740324126379716411/100000000000000000000)
  centralHi := (123935081031594929103/25000000000000000000)
  directionLo := (249094219690510684623/50000000000000000000)
  directionHi := (498188439381021369247/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree103.table
  base := (828503634138068186097933089535643643949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-686741729830223163128788413918060000000000000)
      constant := (14128048507924372306273820536875659882061202141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree103.table
  base := (414248031752565756729791915801039852777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-697969247137607338304782226301000000000000000)
      constant := (14594143855630506093166963327405723083827313586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249094219690510684623/50000000000000000000)
  centralHi := (498188439381021369247/100000000000000000000)
  directionLo := (125156145799174397713/25000000000000000000)
  directionHi := (500624583196697590853/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree104.table
  base := (1219010338616072739798782013550304743551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-693718051263937602073095248796780000000000000)
      constant := (14425913493715989055305784606114879083741785359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree104.table
  base := (1219003660954276213243540262073253979869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-705054573593723565357593855474700000000000000)
      constant := (14901313183755456221895364281510872802414753421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125156145799174397713/25000000000000000000)
  centralHi := (500624583196697590853/100000000000000000000)
  directionLo := (251524464748877247353/50000000000000000000)
  directionHi := (503048929497754494707/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree105.table
  base := (404289394318033929271887943812155231553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-77854930299739115668600231519500000000000000)
      constant := (1636319504065287770595998503639421663029077412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree105.table
  base := (1617151687795864981934011022429522987207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-79126655561093310267822831627600000000000000)
      constant := (1690185719189202489509695587378089189289725407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251524464748877247353/50000000000000000000)
  centralHi := (503048929497754494707/100000000000000000000)
  directionLo := (252730824018760301933/50000000000000000000)
  directionHi := (505461648037520603867/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree106.table
  base := (2022945250382811479255390292969350285969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-707670694131366479961708918554220000000000000)
      constant := (15030934634204748807491890798415799520844248321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree106.table
  base := (202294005652900360483900186014029953227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-719225226505956019463217113822100000000000000)
      constant := (15525218720424296211570926448624024271750908430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252730824018760301933/50000000000000000000)
  centralHi := (505461648037520603867/100000000000000000000)
  directionLo := (253931452268508843771/50000000000000000000)
  directionHi := (507862904537017687543/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree107.table
  base := (2436373267895742017264815221322873104729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-714647015565080918906015753432940000000000000)
      constant := (15338090784459430023055938978874667136508601161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree107.table
  base := (2436368687908224203317762454503756341387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-726310552962072246516028742995800000000000000)
      constant := (15841954925064820482275261443917228432195528283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253931452268508843771/50000000000000000000)
  centralHi := (507862904537017687543/100000000000000000000)
  directionLo := (510252860817796420147/100000000000000000000)
  directionHi := (127563215204449105037/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree108.table
  base := (714360387068247341561655120158742033293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-80180370777643928650035843145740000000000000)
      constant := (1738704887271434665804056425445811552114380372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree108.table
  base := (2857437509949411046368650542820092190899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-81488431046465385952093374685500000000000000)
      constant := (1795764453882146561394805314283875059788528299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (510252860817796420147/100000000000000000000)
  centralHi := (127563215204449105037/25000000000000000000)
  directionLo := (64078959366149771979/12500000000000000000)
  directionHi := (512631674929198175833/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree109.table
  base := (1643075008739000618759622714320112157301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-728599658432509796794629423190380000000000000)
      constant := (15961694235422073062507850695753919010980518218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree109.table
  base := (3286146457060874886878426670967131840043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-740481205874304700621652001343200000000000000)
      constant := (16484994198512356068819211780155419589243566587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64078959366149771979/12500000000000000000)
  centralHi := (512631674929198175833/100000000000000000000)
  directionLo := (257499750635163088657/50000000000000000000)
  directionHi := (102999900254065235463/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree110.table
  base := (3722498608088231670711084289203197978817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-735575979866224235738936258069100000000000000)
      constant := (16278141532818618855483628659485957661486127153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree110.table
  base := (3722495469283672670909031708125537191391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-747566532330420927674463630516900000000000000)
      constant := (16811297264380352633123517272525510700113271919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257499750635163088657/50000000000000000000)
  centralHi := (102999900254065235463/20000000000000000000)
  directionLo := (517356490706992365911/100000000000000000000)
  directionHi := (64669561338374045739/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree111.table
  base := (4166487258517693330210178904794465466589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-82505811255548741631471454771980000000000000)
      constant := (1844187319576764777069389043522090404678597989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree111.table
  base := (166659379665091802675786243666323262691/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-83850206531837461636363917743400000000000000)
      constant := (1904532142361781768058171141068152670156482275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517356490706992365911/100000000000000000000)
  centralHi := (64669561338374045739/12500000000000000000)
  directionLo := (519702790683890654261/100000000000000000000)
  directionHi := (259851395341945327131/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree112.table
  base := (461811591233568992921492619608286624571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-749528622733653113627549927826540000000000000)
      constant := (16920327264217879307552730165908423815945825390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree112.table
  base := (2309056736744305844764146323317074886191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-761737185242653381780086888864300000000000000)
      constant := (17473470247954837227829629040461058812021690238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519702790683890654261/100000000000000000000)
  centralHi := (259851395341945327131/50000000000000000000)
  directionLo := (522038545332232576671/100000000000000000000)
  directionHi := (16313704541632268021/3125000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree113.table
  base := (1269346129417425419144835148272209520789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-756504944167367552571856762705260000000000000)
      constant := (17246065695685323981477378605907136610688598804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree113.table
  base := (5077382368143506061140004329539453702057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-768822511698769608832898518038000000000000000)
      constant := (17809340163382991736416008028816939071711452313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522038545332232576671/100000000000000000000)
  centralHi := (16313704541632268021/3125000000000000000)
  directionLo := (131090973893266921053/25000000000000000000)
  directionHi := (524363895573067684213/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree114.table
  base := (5544293026681904664114455294920387450803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-84831251733453554612907066398220000000000000)
      constant := (1952766796608153488392405687539207927759538603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree114.table
  base := (277214556615098898837944478547737776431/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-86211982017209537320634460801300000000000000)
      constant := (2016488780725235980387168155538053319129940620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131090973893266921053/25000000000000000000)
  centralHi := (524363895573067684213/100000000000000000000)
  directionLo := (105335795843299653813/20000000000000000000)
  directionHi := (263339489608249134533/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree115.table
  base := (6018841395110123904437293307152365172821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-770457587034796430460470432462700000000000000)
      constant := (17906833684545918295435899803283129716330566789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree115.table
  base := (6018839725718665072430382271024769445957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-782993164611002062938521776385400000000000000)
      constant := (18490646836445129801457332715706168827960407413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105335795843299653813/20000000000000000000)
  centralHi := (263339489608249134533/50000000000000000000)
  directionLo := (105796786211397215581/20000000000000000000)
  directionHi := (264491965528493038953/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree116.table
  base := (1625257395466293260574728967040592465143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-777433908468510869404777267341420000000000000)
      constant := (18241863239941077917800102044727092916066129948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree116.table
  base := (3250514055425879950190593421535909113251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-790078491067118289991333405559100000000000000)
      constant := (18836083592258193499789540900019468192864185318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105796786211397215581/20000000000000000000)
  centralHi := (264491965528493038953/50000000000000000000)
  directionLo := (265639441482468762717/50000000000000000000)
  directionHi := (106255776592987505087/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree117.table
  base := (699085754867754236491031432958002809151/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-87156692211358367594342678024460000000000000)
      constant := (2064443314973667701084175556526117653066017510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree117.table
  base := (3495428126282096381550844178015872501973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-88573757502581613004905003859200000000000000)
      constant := (2131634365904865694881348375206788568755263546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265639441482468762717/50000000000000000000)
  centralHi := (106255776592987505087/20000000000000000000)
  directionLo := (106712792794948697979/20000000000000000000)
  directionHi := (66695495496842936237/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree118.table
  base := (117005082184176231118212464067417763787/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-791386551335939747293390937098860000000000000)
      constant := (18921213468174607729642089493096587675679352512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree118.table
  base := (1872081029465432648409040668206976560881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-804249143979350744096956663906500000000000000)
      constant := (19536523938329561062020749599906228457254653316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106712792794948697979/20000000000000000000)
  centralHi := (66695495496842936237/12500000000000000000)
  directionLo := (2679196501847200051/500000000000000000)
  directionHi := (535839300369440010201/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree119.table
  base := (1598686536334334582504003159207240210451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-46962521927626716837511633645740000000000000)
      constant := (1133266714081831768992995037690981848848955135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree119.table
  base := (7993431675663322811981159299239752848091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-47725557084439233597045193710600000000000000)
      constant := (1170089854534583918295769576266803139671821307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2679196501847200051/500000000000000000)
  centralHi := (535839300369440010201/100000000000000000000)
  directionLo := (107621003152429412281/20000000000000000000)
  directionHi := (269052507881073530703/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree120.table
  base := (8506179782806042760801467724039068051329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-89482132689263180575778289650700000000000000)
      constant := (2179216871963849451034356504654225616001506729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree120.table
  base := (1063272362074952375885070618831783397137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-90935532987953688689175546917100000000000000)
      constant := (2249968895414597864131302490096651748927626696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107621003152429412281/20000000000000000000)
  centralHi := (269052507881073530703/50000000000000000000)
  directionLo := (270180615587217008689/50000000000000000000)
  directionHi := (540361231174434017379/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree121.table
  base := (4513283266726746992100979218357997902417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-812315515637083064126311441735020000000000000)
      constant := (19963466592329011729036131240451164745795359106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree121.table
  base := (9026565752836101544854136135069964000699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-825505123347699425255391551427600000000000000)
      constant := (20611101532608345337185484023004602787292362891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270180615587217008689/50000000000000000000)
  centralHi := (540361231174434017379/100000000000000000000)
  directionLo := (21704322604470095043/4000000000000000000)
  directionHi := (135652016277938094019/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree122.table
  base := (9554592905480052059424348765736965667949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-819291837070797503070618276613740000000000000)
      constant := (20317078372695651872445821005644656629321018141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree122.table
  base := (9554592217917728430193067109272445030137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-832590449803815652308203180601300000000000000)
      constant := (20975671948099534212975865599296958665710477033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21704322604470095043/4000000000000000000)
  centralHi := (135652016277938094019/25000000000000000000)
  directionLo := (54484563363606878633/10000000000000000000)
  directionHi := (544845633636068786331/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree123.table
  base := (5045129436096006722185714462893313803061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-91807573167167993557213901276940000000000000)
      constant := (2297087465349965842591258250400451018403523322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree123.table
  base := (10090258266632376370470527713111089198233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-93297308473325764373446089975000000000000000)
      constant := (2371492367179417423377307296947551943004604033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54484563363606878633/10000000000000000000)
  centralHi := (544845633636068786331/100000000000000000000)
  directionLo := (273537025217912170483/50000000000000000000)
  directionHi := (547074050435824340967/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree124.table
  base := (10633564408192757220179230810878118936257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-833244479938226380959231946371180000000000000)
      constant := (21033593038096624362572954354936325886178840113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree124.table
  base := (5316781937445359171301118577761251779107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-846761102716048106413826438948700000000000000)
      constant := (21714379601590106073161804313659626285794231526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273537025217912170483/50000000000000000000)
  centralHi := (547074050435824340967/100000000000000000000)
  directionLo := (274646713446669728731/50000000000000000000)
  directionHi := (549293426893339457463/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree125.table
  base := (11184509489256603934639408526134099048991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-840220801371940819903538781249900000000000000)
      constant := (21396495921969348279903966140588273124637830319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree125.table
  base := (11184509019620470461734180447363636032671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-853846429172164333466638068122400000000000000)
      constant := (22088516838485482907813433885811085355888795439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274646713446669728731/50000000000000000000)
  centralHi := (549293426893339457463/100000000000000000000)
  directionLo := (551503872149777424831/100000000000000000000)
  directionHi := (8617248002340272263/1562500000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree126.table
  base := (11743094092217610234411548410932123848707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-94133013645072806538649512903180000000000000)
      constant := (2418055093247285863039557096353154454130486907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree126.table
  base := (11743093678673205177163725417784378055769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-95659083958697840057716633032900000000000000)
      constant := (2496204779420268308201806274721657167323055169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551503872149777424831/100000000000000000000)
  centralHi := (8617248002340272263/1562500000000000000)
  directionLo := (27685274658388691333/5000000000000000000)
  directionHi := (553705493167773826661/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree127.table
  base := (6154659097435725948299689514948393051379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-854173444239369697792152451007340000000000000)
      constant := (22131592789345516799195318716675973865879462022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree127.table
  base := (3077329457685539164368527351153943012719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-868017082084396787572261326469800000000000000)
      constant := (22846358129982131589822637076552400607938956284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27685274658388691333/5000000000000000000)
  centralHi := (553705493167773826661/100000000000000000000)
  directionLo := (138974598697958382561/25000000000000000000)
  directionHi := (111179678958366706049/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree128.table
  base := (12883181775888778790775990288906566883761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-861149765673084136736459285886060000000000000)
      constant := (22503786771829881618218717150687733824181961249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree128.table
  base := (644159072764482196382525323560774379847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-875102408540513014625072955643500000000000000)
      constant := (23230062183603866781888453637632683349156768460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138974598697958382561/25000000000000000000)
  centralHi := (111179678958366706049/20000000000000000000)
  directionLo := (558082679806591736993/100000000000000000000)
  directionHi := (279041339903295868497/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree129.table
  base := (13464684814738627274108866895279845216809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-96458454122977619520085124529420000000000000)
      constant := (2542119754022006432945682535414142877408920209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree129.table
  base := (13464684532482911599200528413650146457171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-98020859444069915741987176090800000000000000)
      constant := (2624106130575928375458276426696654030935101771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558082679806591736993/100000000000000000000)
  centralHi := (279041339903295868497/50000000000000000000)
  directionLo := (560258448993030698479/100000000000000000000)
  directionHi := (7003230612412883731/1250000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree130.table
  base := (878364205726290761080938727626277764479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-875102408540513014625072955643500000000000000)
      constant := (23257465831986539354004382046448056579019022576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree130.table
  base := (14053827043137340129811039187799851338203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-889273061452745468730696213990900000000000000)
      constant := (24007037104271504622664731482807206719975994027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560258448993030698479/100000000000000000000)
  centralHi := (7003230612412883731/1250000000000000000)
  directionLo := (281212900591369547693/50000000000000000000)
  directionHi := (562425801182739095387/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree131.table
  base := (366265229685127376350091758838570838407/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-882078729974227453569379790522220000000000000)
      constant := (23638950908747517475228277647537764190250778520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree131.table
  base := (7325304484333055144268006611306524855967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-896358387908861695783507843164600000000000000)
      constant := (24400307970433215661131969052651898880706663006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281212900591369547693/50000000000000000000)
  centralHi := (562425801182739095387/100000000000000000000)
  directionLo := (282292416655148367437/50000000000000000000)
  directionHi := (4516678666482373879/800000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree132.table
  base := (476719702611860641227272035533014233789/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-98783894600882432501520736155660000000000000)
      constant := (2669281446227515014270694610875563840706726048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree132.table
  base := (95343939318972014702297629037650512097/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-100382634929441991426257719148700000000000000)
      constant := (2755196419249593068634478917814308637114287520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282292416655148367437/50000000000000000000)
  centralHi := (4516678666482373879/800000000000000000)
  directionLo := (566735640463863128237/100000000000000000000)
  directionHi := (283367820231931564119/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree133.table
  base := (3173418232440326144393647538398150409719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-896031372841656331457993460279660000000000000)
      constant := (24411212153466879658691110453064931514705560355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree133.table
  base := (15867090992725271672291292160291790875359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-910529040821094149889131101512000000000000000)
      constant := (25196416512300737680870973053147020532601278831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566735640463863128237/100000000000000000000)
  centralHi := (283367820231931564119/50000000000000000000)
  directionLo := (17777447372938895289/3125000000000000000)
  directionHi := (568878315934044649249/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree134.table
  base := (3297358241171402281454740936277162564837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-903007694275370770402300295158380000000000000)
      constant := (24801988320597598447241853581937440492401346665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree134.table
  base := (4121697764173267624811458946082295648597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-917614367277210376941942730685700000000000000)
      constant := (25599254187197472936696183988021361835352028692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17777447372938895289/3125000000000000000)
  centralHi := (568878315934044649249/100000000000000000000)
  directionLo := (571012951261111329461/100000000000000000000)
  directionHi := (285506475630555664731/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree135.table
  base := (17114130597621873484908867556026571053181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-101109335078787245482956347781900000000000000)
      constant := (2799540168560402449677123420033225111309323781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree135.table
  base := (4278532616585770747786655061021843056857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-102744410414814067110528262206600000000000000)
      constant := (2889475644172005718217620436828621255163540228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571012951261111329461/100000000000000000000)
  centralHi := (285506475630555664731/50000000000000000000)
  directionLo := (35821227267539431639/6250000000000000000)
  directionHi := (22925585451225236249/4000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree136.table
  base := (17749109321029533151924568773818687956323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42453)
      previous := (30528)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-53938843361341155781818468524460000000000000)
      constant := (1505460690730557756300273248190988333315856771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree136.table
  base := (4437277301374426890197393961025256177101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (41976)
      previous := (31005)
      next := (0)
      square := (490522600808046488271574327410000000000000)
      linear := (-54810883540555460649856822884300000000000000)
      constant := (1553793902527868928653136047997327111023472308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35821227267539431639/6250000000000000000)
  centralHi := (22925585451225236249/4000000000000000000)
  directionLo := (71907307395948061179/12500000000000000000)
  directionHi := (575258459167584489433/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree137.table
  base := (18391727360040562846126731414059417078019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-923936658576514087235220799794540000000000000)
      constant := (25992898996349710917470055752144036894379346771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree137.table
  base := (9195863629186149709163598476748104730479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-938870346645559058100377618206800000000000000)
      constant := (26826900823105131156244830382199142767271565822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71907307395948061179/12500000000000000000)
  centralHi := (575258459167584489433/100000000000000000000)
  directionLo := (144342376619756285551/25000000000000000000)
  directionHi := (115473901295805028441/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree138.table
  base := (1190124043688502866863628825623228584911/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-103434775556692058464391959408140000000000000)
      constant := (2932895919829801980801549601944416280789656176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree138.table
  base := (19041984609552477399407356067859018232023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-105106185900186142794798805264500000000000000)
      constant := (3026943804175699369189646408604501306421491823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144342376619756285551/25000000000000000000)
  centralHi := (115473901295805028441/20000000000000000000)
  directionLo := (579472863195337767673/100000000000000000000)
  directionHi := (289736431597668883837/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree139.table
  base := (3939976264538716102015041678415843520893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-937889301443942965123834469551980000000000000)
      constant := (26802324588417725024638494520560262404902921185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree139.table
  base := (19699881243973703900602102205076353686099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-953040999557791512206000876554200000000000000)
      constant := (27661276586049615525730629797138382363437891491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579472863195337767673/100000000000000000000)
  centralHi := (289736431597668883837/50000000000000000000)
  directionLo := (58156861276015594853/10000000000000000000)
  directionHi := (581568612760155948531/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree140.table
  base := (20365417216165705841303791061257687157361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-944865622877657404068141304430700000000000000)
      constant := (27211682925849263756936461175448981198666663649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree140.table
  base := (2545677143362858224497719397420336709379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-960126326013907739258812505727900000000000000)
      constant := (28083247868165207320151378857823701296238824088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58156861276015594853/10000000000000000000)
  centralHi := (581568612760155948531/100000000000000000000)
  directionLo := (145914209279747197087/25000000000000000000)
  directionHi := (583656837118988788349/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree141.table
  base := (21038592364860461959244257825287452065489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-105760216034596871445827571034380000000000000)
      constant := (3069348698935746557189892727069492662822336889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree141.table
  base := (2629824037990202288200102133890721716259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-107467961385558218479069348322400000000000000)
      constant := (3167600898176727852557257855410748137471917272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145914209279747197087/25000000000000000000)
  centralHi := (583656837118988788349/100000000000000000000)
  directionLo := (585737616756608344991/100000000000000000000)
  directionHi := (18304300523644010781/3125000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree142.table
  base := (10859703377261916444776292771529642317021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-958818265745086281956754974188140000000000000)
      constant := (28039690681801418538012795387379394793998289178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree142.table
  base := (1085970335045564177953782400640293537063/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-974296978926140193364435764075300000000000000)
      constant := (28936757231995141454054644694097772628182155340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585737616756608344991/100000000000000000000)
  centralHi := (18304300523644010781/3125000000000000000)
  directionLo := (587811030733245918219/100000000000000000000)
  directionHi := (29390551536662295911/5000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree143.table
  base := (11203930185601925737002088947565780031547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-965794587178800720901061809066860000000000000)
      constant := (28458340099661760727640864131469054689516967446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree143.table
  base := (22407860324039121595790369757323071493161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-981382305382256420417247393249000000000000000)
      constant := (29368295313055169053531293750140925780583405849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587811030733245918219/100000000000000000000)
  centralHi := (29390551536662295911/5000000000000000000)
  directionLo := (4608415286872212877/781250000000000000)
  directionHi := (589877156719643248257/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree144.table
  base := (5775988300309043179753584315213740220839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-108085656512501684427263182660620000000000000)
      constant := (3208898504853652992404268509921403753257608956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree144.table
  base := (23103953159745814247890235898793593643319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-109829736870930294163339891380300000000000000)
      constant := (3311446925161469265828217345356762137066272719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4608415286872212877/781250000000000000)
  centralHi := (589877156719643248257/100000000000000000000)
  directionLo := (295968035515501296041/50000000000000000000)
  directionHi := (591936071031002592083/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree145.table
  base := (5951921307807736470122189825036916224303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-979747230046229598789675478824300000000000000)
      constant := (29304930013551324133936949190553156687578835708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree145.table
  base := (2975960649341752772770433436728638826893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-995552958294488874522870651596400000000000000)
      constant := (30240938271878027054371477235021795650389905896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295968035515501296041/50000000000000000000)
  centralHi := (591936071031002592083/100000000000000000000)
  directionLo := (593987848659877663027/100000000000000000000)
  directionHi := (148496962164969415757/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree146.table
  base := (4903811289612167276219044200313347354887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-986723551479944037733982313703020000000000000)
      constant := (29732870508959804559415691926775755741152748915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree146.table
  base := (24519056415957892697927226182724387036849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1002638284750605101575682280770100000000000000)
      constant := (30682043149024189673413572567411395176145598241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593987848659877663027/100000000000000000000)
  centralHi := (148496962164969415757/25000000000000000000)
  directionLo := (119206512661609108041/20000000000000000000)
  directionHi := (298016281654022770103/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree147.table
  base := (25238066838850066882526192237225187997043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-110411096990406497408698794286860000000000000)
      constant := (3351545336622989904040244869466302713980308843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree147.table
  base := (252380668106134110091630708960867452781/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-112191512356302369847610434438200000000000000)
      constant := (3458481884176886896383815157598471624468338100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119206512661609108041/20000000000000000000)
  centralHi := (298016281654022770103/50000000000000000000)
  directionLo := (149517571854349467951/25000000000000000000)
  directionHi := (119614057483479574361/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree148.table
  base := (25964716390964362791341844845041886115271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1000676194347372915622595983460460000000000000)
      constant := (30598042575196882130818651948369905512072378839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree148.table
  base := (6491179091532375239726480014671583827727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1016808937662837555681305539117500000000000000)
      constant := (31573819697287127914735373193351788423293045372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149517571854349467951/25000000000000000000)
  centralHi := (119614057483479574361/20000000000000000000)
  directionLo := (60010109219988800441/10000000000000000000)
  directionHi := (600101092199888004411/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree149.table
  base := (2669900509200170144679232897538853492251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1007652515781087354566902818339180000000000000)
      constant := (31035274145439404594319543061165350214001036590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree149.table
  base := (26699005070159792665205132168037211553023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1023894264118953782734117168291200000000000000)
      constant := (32024491367820611042690100325376333085244715407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60010109219988800441/10000000000000000000)
  centralHi := (600101092199888004411/100000000000000000000)
  directionLo := (602125047666569064343/100000000000000000000)
  directionHi := (75265630958321133043/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree150.table
  base := (1715058308111486029455703644111921208499/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-112736537468311310390134405913100000000000000)
      constant := (3497289193338821616985773049573361713012894384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree150.table
  base := (13720466455287492346454010335362634683459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-114553287841674445531880977496100000000000000)
      constant := (3608705774323166292669225397214556425623353718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (602125047666569064343/100000000000000000000)
  centralHi := (75265630958321133043/12500000000000000000)
  directionLo := (604142222655756491519/100000000000000000000)
  directionHi := (471986111449809759/78125000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree151.table
  base := (2819049989234809947640291832757689502919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1021605158648516232455516488096620000000000000)
      constant := (31919028358746822115791003462421127535738308710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree151.table
  base := (14095249937727868584542258734347688015421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1038064917031186236839740426638600000000000000)
      constant := (32935401500271764861648737977908440057505980378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604142222655756491519/100000000000000000000)
  centralHi := (471986111449809759/78125000000000000)
  directionLo := (303076342430173538501/50000000000000000000)
  directionHi := (606152684860347077003/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree152.table
  base := (7236926491985167674872970522398875921949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1028581480082230671399823322975340000000000000)
      constant := (32365551001256537902633148400448461145827616564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree152.table
  base := (180923162206787749834799239971426452981/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1045150243487302463892552055812300000000000000)
      constant := (33395639961636155644664245220114579494053156640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303076342430173538501/50000000000000000000)
  centralHi := (606152684860347077003/100000000000000000000)
  directionLo := (38009781303395323621/6250000000000000000)
  directionHi := (608156500854325177937/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree153.table
  base := (14856275572504579182457236423143672586293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4717)
      previous := (3392)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-6768351643895066080680589267020000000000000)
      constant := (214478239655608584175570911315721963811405658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree153.table
  base := (29712551131947006880740526286485981673141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4664)
      previous := (3445)
      next := (0)
      square := (54502511200894054252397147490000000000000)
      linear := (-6877356666296854189185383562000000000000000)
      constant := (221301093808706035133425283906582355195990573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38009781303395323621/6250000000000000000)
  centralHi := (608156500854325177937/100000000000000000000)
  directionLo := (305076868059242736987/50000000000000000000)
  directionHi := (24406149444739418959/4000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree154.table
  base := (3048503541219653376429957353443212801533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1042534122949659549288436992732780000000000000)
      constant := (33267887356635691859444347075659201684710859970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree154.table
  base := (304850354007110524273163130843823038057/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1059320896399534917998175314159700000000000000)
      constant := (34325683673294200605788142190808305349787631300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305076868059242736987/50000000000000000000)
  centralHi := (24406149444739418959/4000000000000000000)
  directionLo := (30607222753270019189/5000000000000000000)
  directionHi := (612144455065400383781/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree155.table
  base := (15632579379167557680149021325132672407407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1049510444383373988232743827611500000000000000)
      constant := (33723701068977849087271335280048061456769980926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree155.table
  base := (31265158748236413440749560499618039897193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1066406222855651145050986943333400000000000000)
      constant := (34795488923061869801680344696339308695953390937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30607222753270019189/5000000000000000000)
  centralHi := (612144455065400383781/100000000000000000000)
  directionLo := (153532180265914768811/25000000000000000000)
  directionHi := (122825744212731815049/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree156.table
  base := (8013230293110245187123213952608488370949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-117387418424120936353005629165580000000000000)
      constant := (3798067978230829158086479546742458713011353396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree156.table
  base := (8013230290890495419427175820587868206689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-119276838812418596900422063611900000000000000)
      constant := (3918720344642049153358058593707396180822392356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153532180265914768811/25000000000000000000)
  centralHi := (122825744212731815049/20000000000000000000)
  directionLo := (3850666227883774221/625000000000000000)
  directionHi := (616106596461403875361/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree157.table
  base := (32848322643708710160295818005549200682671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1063463087250802866121357497368940000000000000)
      constant := (34644619561681587794602407940586621238780645439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree157.table
  base := (32848322635902417973512890293719175962837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1080576875767883599156610201680800000000000000)
      constant := (35744666209191444336908676087580422190114051333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3850666227883774221/625000000000000000)
  centralHi := (616106596461403875361/100000000000000000000)
  directionLo := (618078142609188812123/100000000000000000000)
  directionHi := (154519535652297203031/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree158.table
  base := (1682568158075321472037691682872376973497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1070439408684517305065664332247660000000000000)
      constant := (35109724341541343660650314325372309451451825460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree158.table
  base := (13460545261857408705148131803180243627/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1087662202223999826209421830854500000000000000)
      constant := (36224038245052407850705875369449615807661107500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618078142609188812123/100000000000000000000)
  centralHi := (154519535652297203031/25000000000000000000)
  directionLo := (605511152228695311/97656250000000000)
  directionHi := (124008683976436799693/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree159.table
  base := (17231021357685562081873260982938139368443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-119712858902025749334441240791820000000000000)
      constant := (3953102904823533479580109231209564200994640486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree159.table
  base := (8615510677334458215488499524911980931379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-121638614297790672584692606669800000000000000)
      constant := (4078511023235196480685657601294934249610067116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605511152228695311/97656250000000000)
  centralHi := (124008683976436799693/20000000000000000000)
  directionLo := (622002487701748594313/100000000000000000000)
  directionHi := (311001243850874297157/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree160.table
  base := (7056072259000839963641909341501888254751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1084392051551946182954278002005100000000000000)
      constant := (36049224967051880962404909160476088510777330795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree160.table
  base := (17640180644850222528062863124031208480023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1101832855136232280315045089201900000000000000)
      constant := (37192349101143766393725340296860893118617716814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622002487701748594313/100000000000000000000)
  centralHi := (311001243850874297157/50000000000000000000)
  directionLo := (623955404556394154857/100000000000000000000)
  directionHi := (311977702278197077429/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree161.table
  base := (36106318890267265869772608726402427830359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1091368372985660621898584836883820000000000000)
      constant := (36523620812224253015183018231200834433080873831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree161.table
  base := (18053159442802506681960993630315822336109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1108918181592348507367856718375600000000000000)
      constant := (37681287920896354443698061328722876170131951162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623955404556394154857/100000000000000000000)
  centralHi := (311977702278197077429/50000000000000000000)
  directionLo := (15647555700553982211/2500000000000000000)
  directionHi := (625902228022159288441/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree162.table
  base := (1477596619647124960895986761802223600877/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-122038299379930562315876852418060000000000000)
      constant := (4111234853188360466071489184070669589647026925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree162.table
  base := (36939915487079938887633021395403722819179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-124000389783162748268963149727700000000000000)
      constant := (4241490629793456368610288193493445083052684579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15647555700553982211/2500000000000000000)
  centralHi := (625902228022159288441/100000000000000000000)
  directionLo := (627843014782415704117/100000000000000000000)
  directionHi := (313921507391207852059/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree163.table
  base := (7556230217581388643578042940595325173203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1105321015853089499787198506641260000000000000)
      constant := (37481703566234747985544646628889499834897545135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree163.table
  base := (4722643885538089618762065228795387709293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1123088834504580961473479976723000000000000000)
      constant := (38668732342648136821121245094618719847094718696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627843014782415704117/100000000000000000000)
  centralHi := (313921507391207852059/50000000000000000000)
  directionLo := (629777820647124924381/100000000000000000000)
  directionHi := (314888910323562462191/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree164.table
  base := (38630025670772605855583475205018471948113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1112297337286803938731505341519980000000000000)
      constant := (37965390474616139105972882171440357409833377217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree164.table
  base := (38630025667606435787721132186110723219789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1130174160960697188526291605896700000000000000)
      constant := (39167237944191009763110105326770665919852040701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629777820647124924381/100000000000000000000)
  centralHi := (314888910323562462191/50000000000000000000)
  directionLo := (631706700571564171101/100000000000000000000)
  directionHi := (315853350285782085551/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree165.table
  base := (9871634807559802855926081754393202151239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-124363739857835375297312464044300000000000000)
      constant := (4272463822624021295649773935276706875181490556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree165.table
  base := (19743269613728207224408270646821267906219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-126362165268534823953233692785600000000000000)
      constant := (4407659163616296583451228438193514235648151238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631706700571564171101/100000000000000000000)
  centralHi := (315853350285782085551/50000000000000000000)
  directionLo := (316814854337269600113/50000000000000000000)
  directionHi := (633629708674539200227/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree166.table
  base := (8070138351382545047337505189411177063789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1126249980154232816620119011277420000000000000)
      constant := (38942055353015000692215499565711911219431183505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree166.table
  base := (8070138350893393951612692046890197156409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1144344813872929642631914864244100000000000000)
      constant := (40173815927495359009523047711238263126171891405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316814854337269600113/50000000000000000000)
  centralHi := (633629708674539200227/100000000000000000000)
  directionLo := (635546898256101161621/100000000000000000000)
  directionHi := (317773449128050580811/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree167.table
  base := (5152810405192220161886294081978159123967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1133226301587947255564425846156140000000000000)
      constant := (39435033322595906869214529999130133815463548024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree167.table
  base := (10305620809847075818355841847312382110451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1151430140329045869684726493417800000000000000)
      constant := (40681888308820550506766400876674692211294189836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635546898256101161621/100000000000000000000)
  centralHi := (317773449128050580811/50000000000000000000)
  directionLo := (318729160907391946349/50000000000000000000)
  directionHi := (637458321814783892699/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree168.table
  base := (8420382734998897889738569175523481494347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80189)
      previous := (57664)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-126689180335740188278748075670540000000000000)
      constant := (4436789812460602676428728627162562876833982735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree168.table
  base := (21050956836552750049638279046067470229813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (79288)
      previous := (58565)
      next := (0)
      square := (926542690415198922290751507330000000000000)
      linear := (-128723940753906899637504235843500000000000000)
      constant := (4577016624034319188888839308169642980135487226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell022.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318729160907391946349/50000000000000000000)
  centralHi := (637458321814783892699/100000000000000000000)
  directionLo := (639364031064377416817/100000000000000000000)
  directionHi := (319682015532188708409/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree169.table
  base := (42988983048295658068682749211720964504011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (721701)
      previous := (518976)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1147178944455376133453039515913580000000000000)
      constant := (40430280321453169774768716391626456058074393499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree169.table
  base := (42988983046635632245122546340733652646459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (713592)
      previous := (527085)
      next := (0)
      square := (8338884213736790300616763565970000000000000)
      linear := (-1165600793241278323790349751765200000000000000)
      constant := (41707599849750044227892880524964984074800958731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell022.Kernel169
