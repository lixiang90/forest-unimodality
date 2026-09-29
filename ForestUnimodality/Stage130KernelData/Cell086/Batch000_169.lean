import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell086.Parameters
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch000_049
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch050_099
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch100_149
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch150_199
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch000_049
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch050_099
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch100_149
import ForestUnimodality.BinomialMassData.Q10787_21012.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree000.table
  base := (45470560065735278610361547/500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (182)
      previous := (91)
      next := (91)
      square := (605987070040295561224041880000000000000)
      linear := (-17088384746015282834169513000000000000)
      constant := (909411201314705572207230940000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree000.table
  base := (45470560065735278610361547/500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (182)
      previous := (91)
      next := (91)
      square := (605987070040295561224041880000000000000)
      linear := (-17088384746015282834169513000000000000)
      constant := (909411201314705572207230940000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree001.table
  base := (514833314798613509685423722637190741462213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-17600605717154528598377947877786457000000000000)
      constant := (14210943248846491168981174638332219029124978681917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree001.table
  base := (256959493191345621728072611808196551009043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-17640396343141049505666821527731957000000000000)
      constant := (14185734227115627320103460998546274147874983246774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9996422451388462003/20000000000000000000)
  directionHi := (390485252007361797/781250000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree002.table
  base := (305286230606047383486841192378120387644651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-34729674391832048768092276706325297000000000000)
      constant := (8442100475095248061993771523041804668749988495859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree002.table
  base := (304318134530607872526256712750799177268877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-34809255643805090582670024006216297000000000000)
      constant := (8415469560438845767376868951091284656249987357893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9996422451388462003/20000000000000000000)
  centralHi := (390485252007361797/781250000000000000)
  directionLo := (70685381029822322087/100000000000000000000)
  directionHi := (8835672628727790261/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree003.table
  base := (191792453627478335575737357750481955536349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-5762082562945507659756289503873793000000000000)
      constant := (592502972408363641830685985240717197656401570349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree003.table
  base := (11938101596181800580227362591619571793311/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-5775346104941014628852580720522293000000000000)
      constant := (590123411491011165993472746387893532555813108976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70685381029822322087/100000000000000000000)
  centralHi := (8835672628727790261/12500000000000000000)
  directionLo := (541072236866470051/625000000000000000)
  directionHi := (86571557898635208161/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree004.table
  base := (128498785356373936422091220440631159740853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-68987811741187089107520934363402977000000000000)
      constant := (3616948506318522893185116473050484125569535349677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree004.table
  base := (127920846417225917731069730349139759671527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-69146974245133172736676428963184977000000000000)
      constant := (3601329558546656241776139875545557333633953081743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541072236866470051/625000000000000000)
  centralHi := (86571557898635208161/100000000000000000000)
  directionLo := (99964224513884620031/100000000000000000000)
  directionHi := (390485252007361797/390625000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree005.table
  base := (45866300674414390168204532525594343644823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-86116880415864609277235263191941817000000000000)
      constant := (2642143127066252652376058552575169370268677330814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree005.table
  base := (91317339902107871015337881932114133633661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-86315833545797213813679631441669317000000000000)
      constant := (2631197298483721726631978591901213658764444336949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99964224513884620031/100000000000000000000)
  centralHi := (390485252007361797/390625000000000000)
  directionLo := (13970425083193555009/12500000000000000000)
  directionHi := (111763400665548440073/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree006.table
  base := (13840902474912891382431158356842924485479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-11471772121171347716327732446720073000000000000)
      constant := (229888566321517391642819655900028699577015497395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree006.table
  base := (17225953722508554367258517545326128222187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-11498299205162361654520314880017073000000000000)
      constant := (229048616651348185946027152719451238321414256748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13970425083193555009/12500000000000000000)
  centralHi := (111763400665548440073/100000000000000000000)
  directionLo := (12243067129601755229/10000000000000000000)
  directionHi := (122430671296017552291/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree007.table
  base := (6813989564855119714806363220690805961717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-120375017765219649616663920849019497000000000000)
      constant := (1720836960941981485111279271143104648898980427624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree007.table
  base := (54287737060727945982136611030639730062287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-120653552147125295967686036398637997000000000000)
      constant := (1715654663115359355359898882952775404846318038583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12243067129601755229/10000000000000000000)
  centralHi := (122430671296017552291/100000000000000000000)
  directionLo := (3306005975839566493/2500000000000000000)
  directionHi := (132240239033582659721/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree008.table
  base := (8856992121885361241745943223846817267741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-137504086439897169786378249677558337000000000000)
      constant := (1504674960447993619444570657592179767537002818345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree008.table
  base := (8822205400053616887203208798727230633901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-137822411447789337044689238877122337000000000000)
      constant := (1501185764672948742238731717005182719284699495545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3306005975839566493/2500000000000000000)
  centralHi := (132240239033582659721/100000000000000000000)
  directionLo := (70685381029822322087/50000000000000000000)
  directionHi := (5654830482385785767/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree009.table
  base := (3672400889235366796898074992551141962641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-17181461679397187772899175389566353000000000000)
      constant := (152316881135552102472223194732727272585992686410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree009.table
  base := (3658340115215859518685793627445244324179/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-17221252305383708680188049039511853000000000000)
      constant := (152069972662710906993665402637104668681771381790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70685381029822322087/50000000000000000000)
  centralHi := (5654830482385785767/4000000000000000000)
  directionLo := (74973168385413465023/50000000000000000000)
  directionHi := (149946336770826930047/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree010.table
  base := (30846943577998906030026899201642404666271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-171762223789252210125806907334636017000000000000)
      constant := (1292267303132000242396387715881163374142723970439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree010.table
  base := (30729183438537544917012022124481843530481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-172160130049117419198695643834091017000000000000)
      constant := (1291063816516100728748028311219606718216684488329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74973168385413465023/50000000000000000000)
  centralHi := (149946336770826930047/100000000000000000000)
  directionLo := (19757164624769600193/12500000000000000000)
  directionHi := (31611463399631360309/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree011.table
  base := (6525200743627485577519133603443867212899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-188891292463929730295521236163174857000000000000)
      constant := (1253662649282452313621546585970267430970159688364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree011.table
  base := (1299976118666285933053336112676595775797/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-189328989349781460275698846312575357000000000000)
      constant := (1253342939481523207185348971824393059284088003460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19757164624769600193/12500000000000000000)
  centralHi := (31611463399631360309/20000000000000000000)
  directionLo := (165771912585701350151/100000000000000000000)
  directionHi := (20721489073212668769/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree012.table
  base := (22160832616197869359800933275347232697021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-22891151237623027829470618332412633000000000000)
      constant := (138452965669146136952060172903103016796299083021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree012.table
  base := (22072160576306082072541588278259430299143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-22944205405605055705855783199006633000000000000)
      constant := (138508305534515592282762221614921392556602737143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165771912585701350151/100000000000000000000)
  centralHi := (20721489073212668769/12500000000000000000)
  directionLo := (541072236866470051/312500000000000000)
  directionHi := (173143115797270416321/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree013.table
  base := (18826024413705539420412285963763134103287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-223149429813284770634949893820252537000000000000)
      constant := (1263962809324795059767051973019179784814308407583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree013.table
  base := (18747555309738228443338197237564570018509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-223666707951109542429705251269544037000000000000)
      constant := (1265253063402358676459633123274910115421867512581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541072236866470051/312500000000000000)
  centralHi := (173143115797270416321/100000000000000000000)
  directionLo := (45053267149600659603/25000000000000000000)
  directionHi := (180213068598402638413/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree014.table
  base := (1596441064739427516000275614270542922669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-240278498487962290804664222648791377000000000000)
      constant := (1303679485746472656172317013609146481430146900210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree014.table
  base := (15894577375699486108519647769211421896917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-240835567251773583506708453748028377000000000000)
      constant := (1305759499989037261703354517424595769226324770253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45053267149600659603/25000000000000000000)
  centralHi := (180213068598402638413/100000000000000000000)
  directionLo := (9350796976637627463/5000000000000000000)
  directionHi := (187015939532752549261/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree015.table
  base := (13484081292181930150761908827967261068651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-28600840795848867886042061275258913000000000000)
      constant := (151410061580893449724001964961078707903745034651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree015.table
  base := (6710894458086259053463247938344677711037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-28667158505826402731523517358501413000000000000)
      constant := (151730102499289440890417536545404354163434306074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9350796976637627463/5000000000000000000)
  centralHi := (187015939532752549261/100000000000000000000)
  directionLo := (48394972094851793403/25000000000000000000)
  directionHi := (193579888379407173613/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree016.table
  base := (5658778031687035258090009486429280841357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-274536635837317331144092880305869057000000000000)
      constant := (1439133963186319463159839744614974298799865260426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree016.table
  base := (5630987325177088107340341959396260097341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-275173285853101665660714858704997057000000000000)
      constant := (1442832591852642196072817920273087363384736860138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48394972094851793403/25000000000000000000)
  centralHi := (193579888379407173613/100000000000000000000)
  directionLo := (99964224513884620031/50000000000000000000)
  directionHi := (199928449027769240063/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree017.table
  base := (4706567995851423804938551609967221790449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-1009223891044964883438779270361273000000000000)
      constant := (5299595608297716830951336039168719107547721938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree017.table
  base := (1872717417415542907851516401241915235247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-1011564516102995525044007132122773000000000000)
      constant := (5315301405297461381389263396645723792883094035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99964224513884620031/50000000000000000000)
  centralHi := (199928449027769240063/100000000000000000000)
  directionLo := (206081528226852262663/100000000000000000000)
  directionHi := (25760191028356532833/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree018.table
  base := (1932485201176582810176808683984828250203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-34310530354074707942613504218105193000000000000)
      constant := (182101111828551799624383819045985398599802592812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree018.table
  base := (7685837215345794015386385782981978160973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-34390111606047749757191251517996193000000000000)
      constant := (182701548110223969368517918905073369523521378973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206081528226852262663/100000000000000000000)
  centralHi := (25760191028356532833/12500000000000000000)
  directionLo := (212056143089466966261/100000000000000000000)
  directionHi := (106028071544733483131/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree019.table
  base := (6234924002879564764386967344181659961103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-325923841861349891653235866791485577000000000000)
      constant := (1760202704758339291396427300546659478101615831927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree019.table
  base := (6195738979157753776363386886226727249343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-326679863755093788891724466140450077000000000000)
      constant := (1766497854909633611396540436919457074508915986087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212056143089466966261/100000000000000000000)
  centralHi := (106028071544733483131/50000000000000000000)
  directionLo := (217866976312717185721/100000000000000000000)
  directionHi := (108933488156358592861/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree020.table
  base := (1225243624886241072952382899058336436487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-343052910536027411822950195620024417000000000000)
      constant := (1894713122132378418541587704597281398613800825532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree020.table
  base := (4866226563749637363766884933694786153877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-343848723055757829968727668618934417000000000000)
      constant := (1901927017547631053071838095808921047383157322893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217866976312717185721/100000000000000000000)
  centralHi := (108933488156358592861/50000000000000000000)
  directionLo := (44705360266219376029/20000000000000000000)
  directionHi := (111763400665548440073/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree021.table
  base := (3705635537740066720526708692762319287639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-40020219912300547999184947160951473000000000000)
      constant := (226869065180594506504867945775888504198220461639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree021.table
  base := (918720317672495989907909979094671227371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-40113064706269096782858985677490973000000000000)
      constant := (227775866571080225960941561368704448561162853484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44705360266219376029/20000000000000000000)
  centralHi := (111763400665548440073/50000000000000000000)
  directionLo := (114523406405609107573/50000000000000000000)
  directionHi := (229046812811218215147/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree022.table
  base := (2630190158012972302017611548072490262131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-377311047885382452162378853277102097000000000000)
      constant := (2201011622289687354675315627773123207945655173179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree022.table
  base := (2603020774763895175447594813156288465071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-378186441657085912122734073575903097000000000000)
      constant := (2210149679435785720059816296416356658811765359639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114523406405609107573/50000000000000000000)
  centralHi := (229046812811218215147/100000000000000000000)
  directionLo := (117218443519613008241/50000000000000000000)
  directionHi := (234436887039226016483/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree023.table
  base := (1658976342478156390445767452363095782181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-394440116560059972332093182105640937000000000000)
      constant := (2371851051262897478889166611485164769781364553629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree023.table
  base := (65400635180249315818740945937232422967/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-395355300957749953199737276054387437000000000000)
      constant := (2381996386247900322953720426816319412611080117575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117218443519613008241/50000000000000000000)
  centralHi := (234436887039226016483/100000000000000000000)
  directionLo := (119852894781799494599/50000000000000000000)
  directionHi := (239705789563598989199/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree024.table
  base := (31154190908866798775627573233084220581/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-45729909470526388055756390103797753000000000000)
      constant := (283775256341601395144524043888056928334639164525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree024.table
  base := (189439702002228088252070201743400188969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-45836017806490443808526719836985753000000000000)
      constant := (285017913718010462122831782359588708891116571876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119852894781799494599/50000000000000000000)
  centralHi := (239705789563598989199/100000000000000000000)
  directionLo := (12243067129601755229/5000000000000000000)
  directionHi := (244861342592035104581/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree025.table
  base := (-10608012070293857727688220075868130429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-428698253909415012671521839762718617000000000000)
      constant := (2747085711222095454738690036035316390752258000278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree025.table
  base := (-39761607396118310374739825572991497523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-429693019559078035353743681011356117000000000000)
      constant := (2759340348818634496520808734582253523710426860293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12243067129601755229/5000000000000000000)
  centralHi := (244861342592035104581/100000000000000000000)
  directionLo := (249910561284711550077/100000000000000000000)
  directionHi := (124955280642355775039/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree026.table
  base := (-75052508413571018286427491792266545301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-445827322584092532841236168591257457000000000000)
      constant := (2950919941962213231402255573154476545185652982910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree026.table
  base := (-153361095034160930583206814756742212043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-446861878859742076430746883489840457000000000000)
      constant := (2964278238801281433308228210951406912451027748065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249910561284711550077/100000000000000000000)
  centralHi := (124955280642355775039/50000000000000000000)
  directionLo := (254859765728733946403/100000000000000000000)
  directionHi := (63714941432183486601/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree027.table
  base := (-354223315000173233573406460574806409187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-51439599028752228112327833046644033000000000000)
      constant := (351696021179328173087914659347888915398504995252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree027.table
  base := (-357791569000310227403910584743797748961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-51558970906711790834194453996480533000000000000)
      constant := (353306648892649062108033915612162640181551300156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254859765728733946403/100000000000000000000)
  centralHi := (63714941432183486601/25000000000000000000)
  directionLo := (259714673695905624481/100000000000000000000)
  directionHi := (129857336847952812241/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree028.table
  base := (-506727251316730067950773538985697385579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-480085459933447573180664826248335137000000000000)
      constant := (3389936655331275333692126006000105067884226415156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree028.table
  base := (-407881359134966918347368628658140672231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-481199597461070158584753288446809137000000000000)
      constant := (3405604058946232078560573314346895922835958679605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259714673695905624481/100000000000000000000)
  centralHi := (129857336847952812241/50000000000000000000)
  directionLo := (3306005975839566493/1250000000000000000)
  directionHi := (264480478067165319441/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree029.table
  base := (-2586124956765203992960599150214852764459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-497214528608125093350379155076873977000000000000)
      constant := (3624784116603495406885542445724688301383843473869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree029.table
  base := (-2597055804264025561873815470982816999379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-498368456761734199661756490925293477000000000000)
      constant := (3641658334607315155852649894224627153123782879589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3306005975839566493/1250000000000000000)
  centralHi := (264480478067165319441/100000000000000000000)
  directionLo := (269161911912331864913/100000000000000000000)
  directionHi := (134580955956165932457/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree030.table
  base := (-309922237844722996277404476812248252897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-57149288586978068168899275989490313000000000000)
      constant := (429964155510111064671920040758919715443695451030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree030.table
  base := (-3108772542078353465689841209542702355573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-57281924006933137859862188155975313000000000000)
      constant := (431977122210895132342249507641076567535110826427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269161911912331864913/100000000000000000000)
  centralHi := (134580955956165932457/50000000000000000000)
  directionLo := (34220412943603440543/12500000000000000000)
  directionHi := (54752660709765504869/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree031.table
  base := (-3570149021756204968350145117789313090453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-531472665957480133689807812733951657000000000000)
      constant := (4124507570004934248105056016256881943978222103923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree031.table
  base := (-3578484574188667447526551768197454471593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-532706175363062281815762895882262157000000000000)
      constant := (4143902977552542087316755061801186643283772513663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34220412943603440543/12500000000000000000)
  centralHi := (54752660709765504869/20000000000000000000)
  directionLo := (278288623403173029681/100000000000000000000)
  directionHi := (139144311701586514841/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree032.table
  base := (-2001117435124387890670697134960073940093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-548601734632157653859522141562490497000000000000)
      constant := (4389182740249067442032069527745026834112816594326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree032.table
  base := (-4009503490870006282950089779447396972209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-549875034663726322892766098360746497000000000000)
      constant := (4409893587518919112113857253422622136922292104119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278288623403173029681/100000000000000000000)
  centralHi := (139144311701586514841/50000000000000000000)
  directionLo := (282741524119289288349/100000000000000000000)
  directionHi := (5654830482385785767/2000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree033.table
  base := (-4398289416004183160434803242976171416689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-62858978145203908225470718932336593000000000000)
      constant := (518180598352631018402216076785355001960260109311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree033.table
  base := (-4404622111348022824838709899223039158303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-63004877107154484885529922315470093000000000000)
      constant := (520632096079815469735372656528217467967603843697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282741524119289288349/100000000000000000000)
  centralHi := (5654830482385785767/2000000000000000000)
  directionLo := (143562687533150678583/50000000000000000000)
  directionHi := (287125375066301357167/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree034.table
  base := (-2380341737733927332694783662669177938147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-2016816166025995481657269201451793000000000000)
      constant := (17120311710894245476733004268533025442575572586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree034.table
  base := (-2383098103647990110670202756372010427567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-2021497416142056764867724924974793000000000000)
      constant := (17201466449709510261110314757756057644730950546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143562687533150678583/50000000000000000000)
  centralHi := (287125375066301357167/100000000000000000000)
  directionLo := (291443292172988280259/100000000000000000000)
  directionHi := (14572164608649414013/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree035.table
  base := (-254570902043782042174851106161521487973/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-599988940656190214368665128048107017000000000000)
      constant := (5241561622675575783375138115018416819643592924860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree035.table
  base := (-5096213249550163775376514945914522948421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-601381612565718446123775705796199517000000000000)
      constant := (5266443562973903131466059286078207579280564390211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291443292172988280259/100000000000000000000)
  centralHi := (14572164608649414013/5000000000000000000)
  directionLo := (147849081919955960951/50000000000000000000)
  directionHi := (295698163839911921903/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree036.table
  base := (-134804556192313185996602863560192010211/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-68568667703429748282042161875182873000000000000)
      constant := (616105932203985850175832392936153207460042551560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree036.table
  base := (-5396350264291116641764530358843137217211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-68727830207375831911197656474964873000000000000)
      constant := (619033540651820453577218511110068005448893856789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147849081919955960951/50000000000000000000)
  centralHi := (295698163839911921903/100000000000000000000)
  directionLo := (299892673541653860093/100000000000000000000)
  directionHi := (149946336770826930047/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree037.table
  base := (-5664402196888993005645552700344315928257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-634247078005545254708093785705184697000000000000)
      constant := (5857906034086313253523028521640974139676832987687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree037.table
  base := (-566802254196499639382089608198225925073/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-635719331167046528277782110753168197000000000000)
      constant := (5885759659106182431554090782026211690645023123430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299892673541653860093/100000000000000000000)
  centralHi := (149946336770826930047/50000000000000000000)
  directionLo := (304029319621688065707/100000000000000000000)
  directionHi := (76007329905422016427/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree038.table
  base := (-2954641044059555941430838580623930499747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-651376146680222774877808114533723537000000000000)
      constant := (6180386326730805264916370714953395123349213568554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree038.table
  base := (-2956212329152409851539500142763240933721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-652888190467710569354785313231652537000000000000)
      constant := (6209783979559770135911989475216163378111468645022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304029319621688065707/100000000000000000000)
  centralHi := (76007329905422016427/25000000000000000000)
  directionLo := (77027608173665621819/25000000000000000000)
  directionHi := (308110432694662487277/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree039.table
  base := (-1531959721175671828609180135012467597877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-74278357261655588338613604818029153000000000000)
      constant := (723596245074927707244337517252014106829766080492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree039.table
  base := (-245222601228281315552399796716028047639/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-74450783307597178936865390634459653000000000000)
      constant := (727038555660937099885186404361695887997769459025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77027608173665621819/25000000000000000000)
  centralHi := (308110432694662487277/100000000000000000000)
  directionLo := (39017273875041096437/12500000000000000000)
  directionHi := (312138191000328771497/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree040.table
  base := (-6320931535119132060582405587521935708579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-685634284029577815217236772190801217000000000000)
      constant := (6853821969084874102351032223094873598360049696789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree040.table
  base := (-632329503627608618888050793489060600963/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-687225909069038651508791718188621217000000000000)
      constant := (6886425230364691126914411401531908633754815693330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39017273875041096437/12500000000000000000)
  centralHi := (312138191000328771497/100000000000000000000)
  directionLo := (316114633996313603089/100000000000000000000)
  directionHi := (31611463399631360309/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree041.table
  base := (-1622321402921534413203812176638115288611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-702763352704255335386951101019340057000000000000)
      constant := (7204733595513314945392463881163684782432121874004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree041.table
  base := (-6491333553233664391918640353591314044147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-704394768369702692585794920667105557000000000000)
      constant := (7238998831076422745702623844927468471193981284677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316114633996313603089/100000000000000000000)
  centralHi := (31611463399631360309/10000000000000000000)
  directionLo := (320041674430516768409/100000000000000000000)
  directionHi := (32004167443051676841/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree042.table
  base := (-829189261218058063865273431260187460093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-79988046819881428395185047760875433000000000000)
      constant := (840564907834733574803654232950699412897339215256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree042.table
  base := (-6635287649594344171130572125145410759611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-80173736407818525962533124793954433000000000000)
      constant := (844561227960374546053297064557166048965621914389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320041674430516768409/100000000000000000000)
  centralHi := (32004167443051676841/10000000000000000000)
  directionLo := (64784221819191275481/20000000000000000000)
  directionHi := (161960554547978188703/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree043.table
  base := (-3377067437767781467728357765352095596691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-737021490053610375726379758676417737000000000000)
      constant := (7934859402973248050105779058785909695372096351562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree043.table
  base := (-26389336045091427540365235309835090607/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-738732486971030774739801325624074237000000000000)
      constant := (7972567744556820699360229561702641341396304393472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64784221819191275481/20000000000000000000)
  centralHi := (161960554547978188703/50000000000000000000)
  directionLo := (40969328554957590081/12500000000000000000)
  directionHi := (327754628439660720649/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree044.table
  base := (-1370317118873437074105608183759941175143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-754150558728287895896094087504956577000000000000)
      constant := (8314047217058571827298615286135015164868167408565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree044.table
  base := (-6852913735118404692735720420324817184339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-755901346271694815816804528102558577000000000000)
      constant := (8353536960285326334960513905903220704691994974949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40969328554957590081/12500000000000000000)
  centralHi := (327754628439660720649/100000000000000000000)
  directionLo := (331543825171402700303/100000000000000000000)
  directionHi := (20721489073212668769/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree045.table
  base := (-6926236069573264523389477133490494021013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-85697736378107268451756490703721713000000000000)
      constant := (966959711984463172853561608897458284341080120987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree045.table
  base := (-3463692287767176910717860870668057281057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-85896689508039872988200858953449213000000000000)
      constant := (971549844983520061482159955360532097666443913886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331543825171402700303/100000000000000000000)
  centralHi := (20721489073212668769/6250000000000000000)
  directionLo := (167645100998322660109/50000000000000000000)
  directionHi := (335290201996645320219/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree046.table
  base := (-6978398854662128961419099911306932678831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-788408696077642936235522745162034257000000000000)
      constant := (9100621350773716435192908912335737024897943276521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree046.table
  base := (-6979391576261283967546735827836938714009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-790239064873022897970810933059527257000000000000)
      constant := (9143794150949094068234787945234620877093187227919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167645100998322660109/50000000000000000000)
  centralHi := (335290201996645320219/100000000000000000000)
  directionLo := (84748794645048198827/25000000000000000000)
  directionHi := (338995178580192795309/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree047.table
  base := (-1401667624761478441593915174749567310647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-805537764752320456405237073990573097000000000000)
      constant := (9507991756174691206705263389983214675919504430885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree047.table
  base := (-280367832905830522813107483230398797243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-807407924173686939047814135538011597000000000000)
      constant := (9553066394186163915811536733623060710632187070325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84748794645048198827/25000000000000000000)
  centralHi := (338995178580192795309/100000000000000000000)
  directionLo := (68532019566413592413/20000000000000000000)
  directionHi := (171330048916033981033/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree048.table
  base := (-350813858885620743797805797464067158203/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-91407425936333108508327933646567993000000000000)
      constant := (1102749162477941625681787785158056596577648875940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree048.table
  base := (-3508508956349174442129961952187802705217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-91619642608261220013868593112943993000000000000)
      constant := (1107973249708822375921945316134503933436003945566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68532019566413592413/20000000000000000000)
  centralHi := (171330048916033981033/50000000000000000000)
  directionLo := (346286231594540832641/100000000000000000000)
  directionHi := (173143115797270416321/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree049.table
  base := (-875300597675549914204503483758962346891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-839795902101675496744665731647650777000000000000)
      constant := (10350868260370207201642755657776511303853828991848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree049.table
  base := (-7003044249171344240112595382465837975957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-841745642775015021201820540494980277000000000000)
      constant := (10399867566929581801609731903256822883948900758387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346286231594540832641/100000000000000000000)
  centralHi := (173143115797270416321/50000000000000000000)
  directionLo := (87468696449649042527/25000000000000000000)
  directionHi := (349874785798596170109/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree050.table
  base := (-1393376103292004785864247109980476793397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-856924970776353016914380060476189617000000000000)
      constant := (10786364746885425820036195260760963892693560207135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree050.table
  base := (-6967432350991443396000504515688257071721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-858914502075679062278823742973464617000000000000)
      constant := (10837387006258024299049540710728550630668617080511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87468696449649042527/25000000000000000000)
  centralHi := (349874785798596170109/100000000000000000000)
  directionLo := (88356726287277902609/25000000000000000000)
  directionHi := (353426905149111610437/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree051.table
  base := (-1727459825375725526282686207097975082769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-336045382334114008875084348060257000000000000)
      constant := (4318042367897507201475469661348089829387614716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree051.table
  base := (-1727578834364228918722152182291183988487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-336825590686790889410160301980757000000000000)
      constant := (4338452092298967457991009352461472066264565668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88356726287277902609/25000000000000000000)
  centralHi := (353426905149111610437/100000000000000000000)
  directionLo := (356943677390347842639/100000000000000000000)
  directionHi := (4461795967379348033/1250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree052.table
  base := (-1707848802670637373036197076317313938261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-891183108125708057253808718133267297000000000000)
      constant := (11685455468655070032425710844913748923327202086604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree052.table
  base := (-6831805714493617896506339503277271633001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-893252220677007144432830147930433297000000000000)
      constant := (11740645119874821332748630438493493376063525708991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356943677390347842639/100000000000000000000)
  centralHi := (4461795967379348033/1250000000000000000)
  directionLo := (14417045487872211073/4000000000000000000)
  directionHi := (180213068598402638413/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree053.table
  base := (-1682911174880662354583403008506274739299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-908312176800385577423523046961806137000000000000)
      constant := (12149043894551798606735077106670830281649242961236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree053.table
  base := (-6731998571963185071109448897887863019167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-910421079977671185509833350408917637000000000000)
      constant := (12206378065763147457363873734310563689108338629497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14417045487872211073/4000000000000000000)
  centralHi := (180213068598402638413/50000000000000000000)
  directionLo := (181937634864447357881/50000000000000000000)
  directionHi := (363875269728894715763/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree054.table
  base := (-6610669330407277895177258347270323290283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-102826805052784788621470819532260553000000000000)
      constant := (1402443469550937966560925664776797748521669031717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree054.table
  base := (-6610974283922109764186627226376976990631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-103065548808703914065204061431933553000000000000)
      constant := (1409056723543572723302201911477540706669748363369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181937634864447357881/50000000000000000000)
  centralHi := (363875269728894715763/100000000000000000000)
  directionLo := (36729201388805265687/10000000000000000000)
  directionHi := (367292013888052656871/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree055.table
  base := (-6468538075548815358342408656194069894677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-942570314149740617762951704618883817000000000000)
      constant := (13104295559655150133712262146014311427079653809907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree055.table
  base := (-3234400394665944257294194922492364738919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-944758798578999267663839755365886317000000000000)
      constant := (13166040583553527503669950875060673423675972927458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36729201388805265687/10000000000000000000)
  centralHi := (367292013888052656871/100000000000000000000)
  directionLo := (23167329081361321939/6250000000000000000)
  directionHi := (14827090612071246041/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree056.table
  base := (-3152654631561742410223988215498797855077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-959699382824418137932666033447422657000000000000)
      constant := (13595955286133704259330657183873270636995649132614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree056.table
  base := (-3152767759294871641493345238406716359669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-961927657879663308740842957844370657000000000000)
      constant := (13659966696012368622856495212516116168221692753958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23167329081361321939/6250000000000000000)
  centralHi := (14827090612071246041/4000000000000000000)
  directionLo := (9350796976637627463/2500000000000000000)
  directionHi := (374031879065505098521/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree057.table
  base := (-3060516111005534643506244467447383483659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-108536494611010628678042262475106833000000000000)
      constant := (1566329893801394598192354533955576508083436044682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree057.table
  base := (-765153377628375424472415566640281337363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-108788501908925261090871795591428333000000000000)
      constant := (1573698612177554691318318390167305613484909637096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9350796976637627463/2500000000000000000)
  centralHi := (374031879065505098521/100000000000000000000)
  directionLo := (94339168066257815431/25000000000000000000)
  directionHi := (15094266890601250469/4000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree058.table
  base := (-7394685839916103324188950228918571077/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-993957520173773178272094691104500337000000000000)
      constant := (14607335682677326093629145883821350652547297845600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree058.table
  base := (-369744771244122167548177497100314135271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-996265376480991390894849362801339337000000000000)
      constant := (14676001891762249396202050625940733129076076936976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94339168066257815431/25000000000000000000)
  centralHi := (15094266890601250469/4000000000000000000)
  directionLo := (190326213150346027533/50000000000000000000)
  directionHi := (380652426300692055067/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree059.table
  base := (-2844746949246512093786739670383803841487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1011086588848450698441809019933039177000000000000)
      constant := (15127054227856751303880107923530971802187546297234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree059.table
  base := (-17780119294318556961867751519827917269/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1013434235781655431971852565279823677000000000000)
      constant := (15198108885021854173237033918508463143926946745280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190326213150346027533/50000000000000000000)
  centralHi := (380652426300692055067/100000000000000000000)
  directionLo := (95979972257975966787/25000000000000000000)
  directionHi := (383919889031903867149/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree060.table
  base := (-5442297746479156023771988470812106017281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-114246184169236468734613705417953113000000000000)
      constant := (1739569317357054184663363994467691642138910436719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree060.table
  base := (-5442421860172264379715835919016370505243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-114511455009146608116539529750923113000000000000)
      constant := (1747734186652244740501472680144882794014554456757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95979972257975966787/25000000000000000000)
  centralHi := (383919889031903867149/100000000000000000000)
  directionLo := (48394972094851793403/12500000000000000000)
  directionHi := (15486391070352573889/4000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree061.table
  base := (-5174185459591151486013983537058276519319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1045344726197805738781237677590116857000000000000)
      constant := (16194543871172653670262041136425626728701422840129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree061.table
  base := (-1034858440221517836670815721266394895713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1047771954382983514125858970236792357000000000000)
      constant := (16270497591886724917998613668512287427500707082915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48394972094851793403/12500000000000000000)
  centralHi := (15486391070352573889/4000000000000000000)
  directionLo := (195186388027956847499/50000000000000000000)
  directionHi := (390372776055913694999/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree062.table
  base := (-488517839038802219427287589763073967699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1062473794872483258950952006418655697000000000000)
      constant := (16742313683531543789082752589403384649676480847090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree062.table
  base := (-2442635084091882030415036436026086955781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1064940813683647555202862172715276697000000000000)
      constant := (16820778042392053868788534931724665811114792967942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195186388027956847499/50000000000000000000)
  centralHi := (390372776055913694999/100000000000000000000)
  directionLo := (393559545470905999937/100000000000000000000)
  directionHi := (196779772735452999969/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree063.table
  base := (-915058920109693749381271943440824220923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-119955873727462308791185148360799393000000000000)
      constant := (1922159199432892599890335856793691048989129305385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree063.table
  base := (-571921686631966105046245499306637482947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-120234408109367955142207263910417893000000000000)
      constant := (1931160949122082613596498578233002359115176120424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393559545470905999937/100000000000000000000)
  centralHi := (196779772735452999969/50000000000000000000)
  directionLo := (9918017927518699479/2500000000000000000)
  directionHi := (396720717100747979161/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree064.table
  base := (-265284335526324931126323895020744746147/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1096731932221838299290380664075733377000000000000)
      constant := (17865900783675230753147660129010676036609871466832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree064.table
  base := (-265288573038299644175724746070944101137/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1099278532284975637356868577672245377000000000000)
      constant := (17949508677292871300937857955757169869355659388272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9918017927518699479/2500000000000000000)
  centralHi := (396720717100747979161/100000000000000000000)
  directionLo := (99964224513884620031/25000000000000000000)
  directionHi := (3198855184444307841/800000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree065.table
  base := (-3892955618207676508251301034397668662451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1113861000896515819460094992904272217000000000000)
      constant := (18441717293238604339903156678808316963849309143941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree065.table
  base := (-3893013872256574362079932935196373104697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1116447391585639678433871780150729717000000000000)
      constant := (18527958098154102973872404606277134375031633039727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99964224513884620031/25000000000000000000)
  centralHi := (3198855184444307841/800000000000000000)
  directionLo := (8059373436397220959/2000000000000000000)
  directionHi := (402968671819861047951/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree066.table
  base := (-3520524282896251750414514136677596951361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-125665563285688148847756591303645673000000000000)
      constant := (2114098002433463914190625164390310864069530222639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree066.table
  base := (-880143580923252859343392404073502137641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-125957361209589302167874998069912673000000000000)
      constant := (2123977389875864032041350139412665878989962225436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8059373436397220959/2000000000000000000)
  centralHi := (402968671819861047951/100000000000000000000)
  directionLo := (203028299760112542153/50000000000000000000)
  directionHi := (406056599520225084307/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree067.table
  base := (-781816152797166651298563193744517220503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1148119138245870859799523650561349897000000000000)
      constant := (19621394714454184310054413105880669223967140933892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree067.table
  base := (-3127307587384476299509351316848508762207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1150785110186967760587878185107698397000000000000)
      constant := (19713023659354035005336216969502950260329081182137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203028299760112542153/50000000000000000000)
  centralHi := (406056599520225084307/100000000000000000000)
  directionLo := (409121221106402693609/100000000000000000000)
  directionHi := (40912122110640269361/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree068.table
  base := (-271318442707376852826325644986269043583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-4032000715988056678094249063632833000000000000)
      constant := (69983581851219421848886006515843334454496515770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree068.table
  base := (-2713221328232955912767297288307564909167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-4041363216220179244515160510678833000000000000)
      constant := (70310170719939462672506492113838704394907825673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409121221106402693609/100000000000000000000)
  centralHi := (40912122110640269361/10000000000000000000)
  directionLo := (206081528226852262663/50000000000000000000)
  directionHi := (412163056453704525327/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree069.table
  base := (-113914517468170022151077607200507473703/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-131375252843913988904328034246491953000000000000)
      constant := (2315384795656256386400185350660742502202382565940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree069.table
  base := (-1139161013867737889018804962272634556903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-131680314309810649193542732229407453000000000000)
      constant := (2326182596239744239364648361781657288601801690194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206081528226852262663/50000000000000000000)
  centralHi := (412163056453704525327/100000000000000000000)
  directionLo := (207591303196283493937/50000000000000000000)
  directionHi := (3321460851140535903/800000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree070.table
  base := (-91129398868674749312034225605547235673/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1199506344269903420308666637046966417000000000000)
      constant := (21461018577658293760852782190339114297578282338860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree070.table
  base := (-22782689584123340266199186908651644579/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1202291688088959883818887792543151417000000000000)
      constant := (21561035592401326885969140172934289499829781823120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207591303196283493937/50000000000000000000)
  centralHi := (3321460851140535903/800000000000000000)
  directionLo := (104545088417806239427/25000000000000000000)
  directionHi := (418180353671224957709/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree071.table
  base := (-336520511994254327626783774427467612773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1216635412944580940478380965875505257000000000000)
      constant := (22092921274549056531804240241265110044883733292172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree071.table
  base := (-1346105379900517240968294951059128398747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1219460547389623924895890995021635757000000000000)
      constant := (22195815888903868220422240318737390997182819693277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104545088417806239427/25000000000000000000)
  centralHi := (418180353671224957709/100000000000000000000)
  directionLo := (84231352771341948017/20000000000000000000)
  directionHi := (210578381928354870043/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree072.table
  base := (-424388284223632594672564224571481536227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-137084942402139828960899477189338233000000000000)
      constant := (2526019015666873371803748321646651582076892963546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree072.table
  base := (-848796586412615165134073537695506908733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-137403267410031996219210466388902233000000000000)
      constant := (2537776016391093627870601025463701844122317713267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84231352771341948017/20000000000000000000)
  centralHi := (210578381928354870043/50000000000000000000)
  directionLo := (424112286178933932523/100000000000000000000)
  directionHi := (106028071544733483131/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree073.table
  base := (-82668732206775878400980872954494926269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1250893550293935980817809623532582937000000000000)
      constant := (23384768083471831879957387682572344900156315510316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree073.table
  base := (-330692100366681641020732475952183963127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1253798265990952007049897399978604437000000000000)
      constant := (23493540276799930583564366499297005229401817893857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424112286178933932523/100000000000000000000)
  centralHi := (106028071544733483131/25000000000000000000)
  directionLo := (427047354322196377499/100000000000000000000)
  directionHi := (170818941728878551/40000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree074.table
  base := (104110001508733254341972740328805911877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1268022618968613500987523952361121777000000000000)
      constant := (24044712022823050884846737980931938919583174289786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree074.table
  base := (6506414868954204137463430374529884497/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1270967125291616048126900602457088777000000000000)
      constant := (24156484199413832714373514778186813447614533711136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427047354322196377499/100000000000000000000)
  centralHi := (170818941728878551/40000000000000000)
  directionLo := (429962387168055805697/100000000000000000000)
  directionHi := (214981193584027902849/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree075.table
  base := (191976450247210610069888150292812118503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-142794631960365669017470920132184513000000000000)
      constant := (2746000321345528698263354770485689936492569266012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree075.table
  base := (76789317237371822010125883935246300611/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-143126220510253343244878200548397013000000000000)
      constant := (2758757316663456290869687045581786809679196266110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429962387168055805697/100000000000000000000)
  centralHi := (214981193584027902849/50000000000000000000)
  directionLo := (432857789493176040801/100000000000000000000)
  directionHi := (216428894746588020401/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree076.table
  base := (134838041273626127406998284501566858401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1302280756317968541326952610018199457000000000000)
      constant := (25392640634699368652952611701682149026048189196090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree076.table
  base := (674184792760124534692002955108570783957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1305304843892944130280907007414057457000000000000)
      constant := (25510535173178473625581315089095008833379293027226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432857789493176040801/100000000000000000000)
  centralHi := (216428894746588020401/50000000000000000000)
  directionLo := (217866976312717185721/50000000000000000000)
  directionHi := (435733952625434371443/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree077.table
  base := (24370526276394195779917767493210546503/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1319409824992646061496666938846738297000000000000)
      constant := (26080625202684593283588928035965841617227896042160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree077.table
  base := (243704102610119788670019923913004866593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1322473703193608171357910209892541797000000000000)
      constant := (26201642122281606021285537438276562692296488330696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217866976312717185721/50000000000000000000)
  centralHi := (435733952625434371443/100000000000000000000)
  directionLo := (438591255061304052741/100000000000000000000)
  directionHi := (219295627530652026371/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree078.table
  base := (2571689400487174289022333818687623705961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-148504321518591509074042363075030793000000000000)
      constant := (2975328506171123551472415278408541631970100131961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree078.table
  base := (1285840722893850148021654725385962935147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-148849173610474690270545934707891793000000000000)
      constant := (2989126295305271788891819852111469721990247274294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438591255061304052741/100000000000000000000)
  centralHi := (219295627530652026371/50000000000000000000)
  directionLo := (55178757880908563589/12500000000000000000)
  directionHi := (441430063047268508713/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree079.table
  base := (3214521065571130924886806159653583568123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1353667962342001101836095596503815977000000000000)
      constant := (27484634658986106787667668843841378947361038175107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree079.table
  base := (3214514248887342686135677031521691978701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1356811421794936253511916614849510477000000000000)
      constant := (27612018746149904625744688776293398883905503202309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55178757880908563589/12500000000000000000)
  centralHi := (441430063047268508713/100000000000000000000)
  directionLo := (444250731127795706703/100000000000000000000)
  directionHi := (27765670695487231669/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree080.table
  base := (3878136046563091240323884147181951974337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1370797031016678622005809925332354817000000000000)
      constant := (28200659484026784426021173523223648467417422947033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree080.table
  base := (775626041198386035612116642074441084289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1373980281095600294588919817327994817000000000000)
      constant := (28331288359227529942157163167750706389749202123005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444250731127795706703/100000000000000000000)
  centralHi := (27765670695487231669/6250000000000000000)
  directionLo := (447053602662193760291/100000000000000000000)
  directionHi := (111763400665548440073/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree081.table
  base := (4562533454675336348191748979842196558939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-154214011076817349130613806017877073000000000000)
      constant := (3214003445126325396027887801282293324991903532939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree081.table
  base := (1140632112799677175431864138465121592001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-154572126710696037296213668867386573000000000000)
      constant := (3228882830342954851147659553825003294314786632004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447053602662193760291/100000000000000000000)
  centralHi := (111763400665548440073/25000000000000000000)
  directionLo := (449839010312480790139/100000000000000000000)
  directionHi := (22491950515624039507/5000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree082.table
  base := (1316928134547962539327193727922472573811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1405055168366033662345238582989432497000000000000)
      constant := (29660749204573680688892908307324131087015975593196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree082.table
  base := (2633854126233202479590293646254344517477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1408317999696928376742926222284963497000000000000)
      constant := (29797990067527142296504757689336009059308721990586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449839010312480790139/100000000000000000000)
  centralHi := (22491950515624039507/5000000000000000000)
  directionLo := (452607276504231404693/100000000000000000000)
  directionHi := (226303638252115702347/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree083.table
  base := (599367266136671653570082294635902291399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1422184237040711182514952911817971337000000000000)
      constant := (30404814061794262268487988231341147299019846285910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree083.table
  base := (599366899095985940576616844340642953291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1425486858997592417819929424763447837000000000000)
      constant := (30545422125473032888693015230712952641938984336190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452607276504231404693/100000000000000000000)
  centralHi := (226303638252115702347/50000000000000000000)
  directionLo := (455358713862207059947/100000000000000000000)
  directionHi := (113839678465551764987/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree084.table
  base := (6740413286570575705446188949432115918413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-159923700635043189187185248960723353000000000000)
      constant := (3462025062551480434517780053156803938837970176413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree084.table
  base := (3370205071790686512283400452912073011419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-160295079810917384321881403026881353000000000000)
      constant := (3478026848054433646926844305057081884530167330838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455358713862207059947/100000000000000000000)
  centralHi := (113839678465551764987/25000000000000000000)
  directionLo := (114523406405609107573/25000000000000000000)
  directionHi := (458093625622436430293/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree085.table
  base := (7507933959185014349766450254400615828853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-5039592990969087276312738994723353000000000000)
      constant := (110453230780401802860830800700584617699954713293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree085.table
  base := (469245704262310020369457817127840618027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-5051296116259240484338878303530853000000000000)
      constant := (110963489883659179663123366257916219850797375792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114523406405609107573/25000000000000000000)
  centralHi := (458093625622436430293/100000000000000000000)
  directionLo := (460812306022283360479/100000000000000000000)
  directionHi := (2880076912639271003/625000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree086.table
  base := (829623429482181760045289883184178518571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1473571443064743743024095898303587857000000000000)
      constant := (32693088448905841756280946100272041213990548411390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree086.table
  base := (8296231991141646544260903245871749117/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1476993436899584541050939032198900857000000000000)
      constant := (32844042946824918512931125962381097102480240053000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460812306022283360479/100000000000000000000)
  centralHi := (2880076912639271003/625000000000000000)
  directionLo := (7242422510467542483/1562500000000000000)
  directionHi := (463515040669922718913/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree087.table
  base := (4552656984254591594954489991469759392623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-165633390193269029243756691903569633000000000000)
      constant := (3719393312678356806960474981454707961035083021246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree087.table
  base := (569081999790759699637979860347408257607/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-166018032911138731347549137186376133000000000000)
      constant := (3736558303902108322222131699357814744793701113712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7242422510467542483/1562500000000000000)
  centralHi := (463515040669922718913/100000000000000000000)
  directionLo := (93240421378907483969/20000000000000000000)
  directionHi := (233101053447268709923/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree088.table
  base := (2483793176385530700244670596567654006741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1507829580414098783363524555960665537000000000000)
      constant := (34265337783554017625901589770122492131083588858676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree088.table
  base := (9935171017929619021713017363966857944579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1511331155500912623204945437155869537000000000000)
      constant := (34423393933897621739649083566467192979824434427211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93240421378907483969/20000000000000000000)
  centralHi := (233101053447268709923/50000000000000000000)
  directionLo := (93774754815690406593/20000000000000000000)
  directionHi := (234436887039226016483/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree089.table
  base := (2157162054748180730497816663295036077563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1524958649088776303533238884789204377000000000000)
      constant := (35065482350845491210071610251122517146397990600335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree089.table
  base := (5392904414790423790581960712615815165777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1528500014801576664281948639634353877000000000000)
      constant := (35227150536941357306185861629610490923703574059986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93774754815690406593/20000000000000000000)
  centralHi := (234436887039226016483/50000000000000000000)
  directionLo := (1886121215889315467/400000000000000000)
  directionHi := (471530303972328866751/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree090.table
  base := (2914306619225206398108130532198010410653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-171343079751494869300328134846415913000000000000)
      constant := (3986108167840617528146392835576884573468290034612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree090.table
  base := (582861262061274755367234989739541434353/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-171740986011360078373216871345870913000000000000)
      constant := (4004477170999647180571227315842670083045354647060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1886121215889315467/400000000000000000)
  centralHi := (471530303972328866751/100000000000000000000)
  directionLo := (237085975497235202317/50000000000000000000)
  directionHi := (94834390198894080927/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree091.table
  base := (12549421149249993865109297369092197222251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1559216786438131343872667542446282057000000000000)
      constant := (36693811258139906099803535214108275391480569094259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree091.table
  base := (12549420092089289135991772894608048672817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1562837733402904746435955044591322557000000000000)
      constant := (36862825935627616975167294812139259707300150353353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237085975497235202317/50000000000000000000)
  centralHi := (94834390198894080927/20000000000000000000)
  directionLo := (476798962515196781603/100000000000000000000)
  directionHi := (119199740628799195401/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree092.table
  base := (13462394150759972509925438646365216596839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1576345855112808864042381871274820897000000000000)
      constant := (37521995589704590327377055668556184498060124737551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree092.table
  base := (538495729857249195508181356748113213411/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1580006592703568787512958247069806897000000000000)
      constant := (37694744723088095986682830179466491737597051367475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476798962515196781603/100000000000000000000)
  centralHi := (119199740628799195401/25000000000000000000)
  directionLo := (119852894781799494599/25000000000000000000)
  directionHi := (479411579127197978397/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree093.table
  base := (899759085198630035283328676031724835343/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-177052769309720709356899577789262193000000000000)
      constant := (4262169611332949432587660682594679126530183573488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree093.table
  base := (14396144589676135834111362247538581981653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-177463939111581425398884605505365693000000000000)
      constant := (4281783433135185896601903521093960950144330079653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119852894781799494599/25000000000000000000)
  centralHi := (479411579127197978397/100000000000000000000)
  directionLo := (482010034902697011321/100000000000000000000)
  directionHi := (241005017451348505661/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree094.table
  base := (3070134937334058615732888363485027918763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1610603992462163904381810528931898577000000000000)
      constant := (39206403992260948814555278172663786401777987454335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree094.table
  base := (7675337012571877017268675689048284722939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1614344311304896869666964652026775577000000000000)
      constant := (39386744458345552453602939507158272670658682544902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482010034902697011321/100000000000000000000)
  centralHi := (241005017451348505661/50000000000000000000)
  directionLo := (484594557638202096381/100000000000000000000)
  directionHi := (242297278819101048191/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree095.table
  base := (4081495509245199542833932154460959044813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1627733061136841424551524857760437417000000000000)
      constant := (40062628058172846459829892777932901053624805301268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree095.table
  base := (16325981471282434312799512912444727560783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1631513170605560910743967854505259917000000000000)
      constant := (40246825401224397170313808663904931108064794149047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484594557638202096381/100000000000000000000)
  centralHi := (242297278819101048191/50000000000000000000)
  directionLo := (487165369087572106797/100000000000000000000)
  directionHi := (243582684543786053399/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree096.table
  base := (8661033671514359658814923667218023837333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-182762458867946549413471020732108473000000000000)
      constant := (4547577633085647942506259337172829584606573630666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree096.table
  base := (2165258357416194645503832357805675269037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-183186892211802772424552339664860473000000000000)
      constant := (4568477080550641208674317603437362393444341688296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487165369087572106797/100000000000000000000)
  centralHi := (243582684543786053399/50000000000000000000)
  directionLo := (12243067129601755229/2500000000000000000)
  directionHi := (489722685184070209161/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree097.table
  base := (9169465272437372067219502791877809006787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1661991198486196464890953515417515097000000000000)
      constant := (41803115909400937957381314071532537343767123078166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree097.table
  base := (4584732532833226585725831799327267545359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1665850889206888992897974259462228597000000000000)
      constant := (41995149427940539600224576613027499593618176616924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12243067129601755229/2500000000000000000)
  centralHi := (489722685184070209161/100000000000000000000)
  directionLo := (246133358126017490987/50000000000000000000)
  directionHi := (19690668650081399279/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree098.table
  base := (19376571592000750035045440639231152314609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1679120267160873985060667844246053937000000000000)
      constant := (42687379691669168354983839663727238691049691577481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree098.table
  base := (1937657123847732648294171150765643548563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1683019748507553033974977461940712937000000000000)
      constant := (42883392508831697500262031509835975283198393590670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246133358126017490987/50000000000000000000)
  centralHi := (19690668650081399279/4000000000000000000)
  directionLo := (494797667208756254611/100000000000000000000)
  directionHi := (123699416802189063653/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree099.table
  base := (2554373805231784158027712652628545043089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-188472148426172389470042463674954753000000000000)
      constant := (4842332227044592178614443413719640153345247336712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree099.table
  base := (2043499013966958968414492233472644544967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-188909845312024119450220073824355253000000000000)
      constant := (4864558107388368630852171941958736777225133669670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494797667208756254611/100000000000000000000)
  centralHi := (123699416802189063653/25000000000000000000)
  directionLo := (99463147551420810091/20000000000000000000)
  directionHi := (62164467219638006307/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree100.table
  base := (4302837411723415265601077169699996469157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1713378404510229025400096501903131617000000000000)
      constant := (44483946963609052947247231298662511599349432402065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree100.table
  base := (10757093400170827236691585006470106022591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1717357467108881116128983866897681617000000000000)
      constant := (44688040799977529284925207842205375902636660514638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99463147551420810091/20000000000000000000)
  centralHi := (62164467219638006307/12500000000000000000)
  directionLo := (99964224513884620031/20000000000000000000)
  directionHi := (124955280642355775039/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree101.table
  base := (11307080706081668603993614479953132836211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1730507473184906545569810830731670457000000000000)
      constant := (45396250451461046170227177949690452558621203719798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree101.table
  base := (22614161191438640247088021972406539172839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1734526326409545157205987069376165957000000000000)
      constant := (45604446008476591685160219843116739211844171921551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99964224513884620031/20000000000000000000)
  centralHi := (124955280642355775039/25000000000000000000)
  directionLo := (100462802292634432097/20000000000000000000)
  directionHi := (251157005731586080243/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree102.table
  base := (23734913477178287536702846024160635354287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-671909473994457541614580991757097000000000000)
      constant := (17807727991641204663708228813006659180473630783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree102.table
  base := (1483432080535189565395910281003654698913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-673469890699811302684732899598097000000000000)
      constant := (17889365087012410480051666197973760863212288272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100462802292634432097/20000000000000000000)
  centralHi := (251157005731586080243/50000000000000000000)
  directionLo := (504794589568756605693/100000000000000000000)
  directionHi := (252397294784378302847/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree103.table
  base := (24876443232412614602987579295084952203487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (473382)
      previous := (236691)
      next := (236691)
      square := (1576172369174808754743732929880000000000000)
      linear := (-166346084506952736912926712073593000000000000)
      constant := (4453661714338380686330975107093237460681269687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree103.table
  base := (24876443071251030406203171729875467392171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (473382)
      previous := (236691)
      next := (236691)
      square := (1576172369174808754743732929880000000000000)
      linear := (-166732401264103425333207038772093000000000000)
      constant := (4474070934861053337345318627161083840687036771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504794589568756605693/100000000000000000000)
  centralHi := (252397294784378302847/50000000000000000000)
  directionLo := (253631518744987123321/50000000000000000000)
  directionHi := (507263037489974246643/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree104.table
  base := (26038750660051739274834122853870609223061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1781894679208939106078953817217286977000000000000)
      constant := (48189240314440792626267991467666601663736628241549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree104.table
  base := (6509687630590161905365249242935410793447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1786032904311537280436996676811618977000000000000)
      constant := (48409985877868481196772466927989492885412294636092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253631518744987123321/50000000000000000000)
  centralHi := (507263037489974246643/100000000000000000000)
  directionLo := (254859765728733946403/50000000000000000000)
  directionHi := (509719531457467892807/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree105.table
  base := (6805458936295573736472135901534234132841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-199891527542624069583185349560647313000000000000)
      constant := (5459881118546887725877455880575768756042098555364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree105.table
  base := (13610917813777174781612029062091861875339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-200355751512466813501555542143344813000000000000)
      constant := (5484882286745149845317565317365433192453302498678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254859765728733946403/50000000000000000000)
  centralHi := (509719531457467892807/100000000000000000000)
  directionLo := (256082121737776817143/50000000000000000000)
  directionHi := (512164243475553634287/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree106.table
  base := (14212849237670425669173762247755714206643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1816152816558294146418382474874364657000000000000)
      constant := (50097966384515555413916072052614711212239069603574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree106.table
  base := (14212849187430814761905131979096163718973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1820370622912865362591003081768587657000000000000)
      constant := (50327282656124202819327008105938050066553628865514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256082121737776817143/50000000000000000000)
  centralHi := (512164243475553634287/100000000000000000000)
  directionLo := (514597341462771031819/100000000000000000000)
  directionHi := (25729867073138551591/5000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree107.table
  base := (7412584710033056873582645111567646047881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1833281885232971666588096803702903497000000000000)
      constant := (51066349266934645552416516123861098928116170979716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree107.table
  base := (29650338754309204181077861885272381638827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1837539482213529403668006284247071997000000000000)
      constant := (51300012103846840961428498256734240559143226987443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514597341462771031819/100000000000000000000)
  centralHi := (25729867073138551591/5000000000000000000)
  directionLo := (517018989386480222389/100000000000000000000)
  directionHi := (51701898938648022239/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree108.table
  base := (30895756830906684913914798602819991219543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-205601217100849909639756792503493593000000000000)
      constant := (5782675412660064331820435086919732669899110057543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree108.table
  base := (15447878378804197425321553482628889084907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-206078704612688160527223276302839593000000000000)
      constant := (5809125435960616128883062787927202462126427893814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517018989386480222389/100000000000000000000)
  centralHi := (51701898938648022239/10000000000000000000)
  directionLo := (259714673695905624481/50000000000000000000)
  directionHi := (519429347391811248963/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree109.table
  base := (16080976220243469499265246777436219876991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1867540022582326706927525461359981177000000000000)
      constant := (53031154725335305660009777741525562556923337093838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree109.table
  base := (32161952377890873176107711136323932724809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1871877200814857485822012689204040677000000000000)
      constant := (53273633115330790700402799041407214730773774069281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259714673695905624481/50000000000000000000)
  centralHi := (519429347391811248963/100000000000000000000)
  directionLo := (8153571436332071699/1562500000000000000)
  directionHi := (521828571925252588737/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree110.table
  base := (6689785132587464160052659098336387356967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1884669091257004227097239790188520017000000000000)
      constant := (54027577300955036670924332349817951283778168053515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree110.table
  base := (33448925609485309490732071109247863221793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1889046060115521526899015891682525017000000000000)
      constant := (54274524678746082860928220493102169703472925038137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8153571436332071699/1562500000000000000)
  centralHi := (521828571925252588737/100000000000000000000)
  directionLo := (262108407926574389461/50000000000000000000)
  directionHi := (524216815853148778923/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree111.table
  base := (271536535104442191701079517849268987663/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-211310906659075749696328235446339873000000000000)
      constant := (6114816271184984285393027678198726185876799444864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree111.table
  base := (6951335289545722498745761366004194264679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-211801657712909507552891010462334373000000000000)
      constant := (6142755957084749806466897863792550369848500393395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262108407926574389461/50000000000000000000)
  centralHi := (524216815853148778923/100000000000000000000)
  directionLo := (526594228575361125409/100000000000000000000)
  directionHi := (52659422857536112541/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree112.table
  base := (9021301231943245599093974874709009774961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1918927228606359267436668447845597697000000000000)
      constant := (56048462144354180199070866056469711736445447234596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree112.table
  base := (18042602444403210974682456913902550273249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1923383778716849609053022296639493697000000000000)
      constant := (56304469920275533401550321237534217278725970730482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526594228575361125409/100000000000000000000)
  centralHi := (52659422857536112541/10000000000000000000)
  directionLo := (3306005975839566493/625000000000000000)
  directionHi := (528960956134330638881/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree113.table
  base := (7486902192576924937778084058255923832737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1936056297281036787606382776674136537000000000000)
      constant := (57072924411932883897613637066459151071219296363165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree113.table
  base := (37434510929618339180029207194222793433517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1940552638017513650130025499117978037000000000000)
      constant := (57333523598198885861959350748443529817259608999653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3306005975839566493/625000000000000000)
  centralHi := (528960956134330638881/100000000000000000000)
  directionLo := (531317141319768493917/100000000000000000000)
  directionHi := (265658570659884246959/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree114.table
  base := (38804594596061754121430008026622621231457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-217020596217301589752899678389186153000000000000)
      constant := (6456303693703119172013228642083292320318268393457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree114.table
  base := (38804594567664076311224497700482170948819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-217524610813130854578558744621829153000000000000)
      constant := (6485773849718201408146411444089656086111250002819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531317141319768493917/100000000000000000000)
  centralHi := (265658570659884246959/50000000000000000000)
  directionLo := (533662923769186374739/100000000000000000000)
  directionHi := (26683146188459318737/5000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree115.table
  base := (321563646601496381357275789357242684739/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1970314434630391827945811434331214217000000000000)
      constant := (59149888638481320719997715768086873124734016081375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree115.table
  base := (4019545580094729409674187435843544755291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1974890356618841732284031904074946717000000000000)
      constant := (59419793068015226832498436076937193264444026516190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533662923769186374739/100000000000000000000)
  centralHi := (26683146188459318737/5000000000000000000)
  directionLo := (66999805008058373551/12500000000000000000)
  directionHi := (535998440064466988409/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree116.table
  base := (20803547324291733660879474807088942746869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1987443503305069348115525763159753057000000000000)
      constant := (60202390597346352211258111501366589941915175815642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree116.table
  base := (1664283785115775849986385629286042230697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-1992059215919505773361035106553431057000000000000)
      constant := (60477008859809706509397866115086031689205827356825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66999805008058373551/12500000000000000000)
  centralHi := (535998440064466988409/100000000000000000000)
  directionLo := (538323823824663729827/100000000000000000000)
  directionHi := (134580955956165932457/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree117.table
  base := (21519755532471582997861922075277679583331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-222730285775527429809471121332032433000000000000)
      constant := (6807137679987453141972087392990198910260344858662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree117.table
  base := (43039511047285969522042343287879707804791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-223247563913352201604226478781323933000000000000)
      constant := (6838179113645955911541971441669340044259197010791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538323823824663729827/100000000000000000000)
  centralHi := (134580955956165932457/25000000000000000000)
  directionLo := (270319602897603957619/50000000000000000000)
  directionHi := (540639205795207915239/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree118.table
  base := (44492705073267449390138768566953116195437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2021701640654424388454954420816830737000000000000)
      constant := (62335434206075940939928235925869610401874934336933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree118.table
  base := (22246352529099457574330642358447221046843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2026396934520833855515041511510399737000000000000)
      constant := (62619602557001444920302457096155991835683150327174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270319602897603957619/50000000000000000000)
  centralHi := (540639205795207915239/100000000000000000000)
  directionLo := (67868089241711513667/12500000000000000000)
  directionHi := (542944713933692109337/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree119.table
  base := (45966676672816088622678428021355740487977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-7054777540931148472749718856904393000000000000)
      constant := (219432442407932575485659223326788316957532531937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree119.table
  base := (919333533199152374168282228800382349627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-7071161916337362963986313889234893000000000000)
      constant := (220432458347247711931680208802411271106236779350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67868089241711513667/12500000000000000000)
  centralHi := (542944713933692109337/100000000000000000000)
  directionLo := (17038764796637150217/3125000000000000000)
  directionHi := (109048094698477761389/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree120.table
  base := (23730712931532270457792698661167628644803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-228439975333753269866042564274878713000000000000)
      constant := (7167318229924702685100033554786593281185189285606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree120.table
  base := (1186535646302319010720132680532080855539/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-228970517013573548629894212940818713000000000000)
      constant := (7199971748762231585967888165641293427406537181560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17038764796637150217/3125000000000000000)
  centralHi := (109048094698477761389/20000000000000000000)
  directionLo := (34220412943603440543/6250000000000000000)
  directionHi := (547526607097655048689/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree121.table
  base := (1959078105746714305439229617268863833201/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2073088846678456948964097407302447257000000000000)
      constant := (65605098846355851975882396223834468915328072320225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree121.table
  base := (24488476317153291812989037284978692605271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2077903512422825978746051118945852757000000000000)
      constant := (65903898386509715196054541912109977650366162842878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34220412943603440543/6250000000000000000)
  centralHi := (547526607097655048689/100000000000000000000)
  directionLo := (549803234826365410171/100000000000000000000)
  directionHi := (137450808706591352543/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree122.table
  base := (3157078563401890431055882918107344416161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2090217915353134469133811736130986097000000000000)
      constant := (66713680186987695062210611946747790625570342071184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree122.table
  base := (789269640725681584272550784479431234399/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2095072371723490019823054321424337097000000000000)
      constant := (67017438405299191560069361477978794382500775397824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549803234826365410171/100000000000000000000)
  centralHi := (137450808706591352543/25000000000000000000)
  directionLo := (552070474279508167701/100000000000000000000)
  directionHi := (276035237139754083851/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree123.table
  base := (52070338975279416923793328666665402885691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-234149664891979109922614007217724993000000000000)
      constant := (7536845343468428733889764545259476223412931491691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree123.table
  base := (10414067793693207190220639335256696407681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-234693470113794895655561947100313493000000000000)
      constant := (7571151755025274363301210884395684594963231768405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552070474279508167701/100000000000000000000)
  centralHi := (276035237139754083851/50000000000000000000)
  directionLo := (138582110163268068929/25000000000000000000)
  directionHi := (554328440653072275717/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree124.table
  base := (13412049631561240233752440595059922005973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2124476052702489509473240393788063777000000000000)
      constant := (68958882559041159199807179164171407051488468063028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree124.table
  base := (2682409926021642778842279043985665982803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2129410090324818101977060726381305777000000000000)
      constant := (69272680556296177151810438138311068413009196544540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138582110163268068929/25000000000000000000)
  centralHi := (554328440653072275717/100000000000000000000)
  directionLo := (556577246806346059363/100000000000000000000)
  directionHi := (139144311701586514841/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree125.table
  base := (55246835667440158133294976610090862889821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2141605121377167029642954722616602617000000000000)
      constant := (70095503590466722673948745779045768573899486682389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree125.table
  base := (11049367132496500886446876747947518526791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2146578949625482143054063928859790117000000000000)
      constant := (70414382688509134883927995957887106945029687975595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556577246806346059363/100000000000000000000)
  centralHi := (139144311701586514841/25000000000000000000)
  directionLo := (139704250831935550091/25000000000000000000)
  directionHi := (111763400665548440073/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree126.table
  base := (14216562599761665435509999396426818763887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-239859354450204949979185450160571273000000000000)
      constant := (7915719020610840174234856860028234234027585223548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree126.table
  base := (56866250394818113962915871529278391196657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-240416423214016242681229681259808273000000000000)
      constant := (7951719132430216408555879722293409507187341558657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139704250831935550091/25000000000000000000)
  centralHi := (111763400665548440073/20000000000000000000)
  directionLo := (28052390929912882389/5000000000000000000)
  directionHi := (561047818598257647781/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree127.table
  base := (11701288544260325307271040021000199917701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2175863258726522069982383380273680297000000000000)
      constant := (72396785344140219933300865705963384629154203266545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree127.table
  base := (58506442717695183526567934572997574585137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2180916668226810225208070333816758797000000000000)
      constant := (72725949066391665782610460691291536537830441644233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28052390929912882389/5000000000000000000)
  centralHi := (561047818598257647781/100000000000000000000)
  directionLo := (563269798852671491991/100000000000000000000)
  directionHi := (70408724856583936499/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree128.table
  base := (60167412634486897295078239931387728716789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2192992327401199590152097709102219137000000000000)
      constant := (73561446066402474996874056958848192624700634117101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree128.table
  base := (60167412631411224695531653387867570520511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2198085527527474266285073536295243137000000000000)
      constant := (73895813312076498737755409456694721687751115218599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563269798852671491991/100000000000000000000)
  centralHi := (70408724856583936499/12500000000000000000)
  directionLo := (282741524119289288349/50000000000000000000)
  directionHi := (565483048238578576699/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree129.table
  base := (15462290034729984490822262945556438815039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-245569044008430790035756893103417553000000000000)
      constant := (8303939261365898540198999635913192142353393556156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree129.table
  base := (15462290034074270043667151603833500846611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-246139376314237589706897415419303053000000000000)
      constant := (8341673880992841757668144281790855282966840690444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282741524119289288349/50000000000000000000)
  centralHi := (565483048238578576699/100000000000000000000)
  directionLo := (567687668873351667973/100000000000000000000)
  directionHi := (283843834436675833987/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree130.table
  base := (7943960654368278837248324558514139876889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2227250464750554630491526366759296817000000000000)
      constant := (75918807201821588765801253736673284204121071664008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree130.table
  base := (3971980327044353503450402725087211776301/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2232423246128802348439079941252211817000000000000)
      constant := (76263703916978745496277618523219196658142492491344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567687668873351667973/100000000000000000000)
  centralHi := (283843834436675833987/50000000000000000000)
  directionLo := (113976752179824066249/20000000000000000000)
  directionHi := (284941880449560165623/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree131.table
  base := (65274987922932915753224251981811303467671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2244379533425232150661240695587835657000000000000)
      constant := (77111507614998111580379439198024519703688644783039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree131.table
  base := (104439980673641354456637753949789292471/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2249592105429466389516083143730696157000000000000)
      constant := (77461730276216407791447022384815302743592753899375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113976752179824066249/20000000000000000000)
  centralHi := (284941880449560165623/50000000000000000000)
  directionLo := (143017855633962566947/25000000000000000000)
  directionHi := (572071422535850267789/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree132.table
  base := (67019068203263478513875048033827624912217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-251278733566656630092328336046263833000000000000)
      constant := (8701506065759248578298567550329049117808482234217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree132.table
  base := (16754767050409366103696016981825297481679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-251862329414458936732565149578797833000000000000)
      constant := (8741016000739930487826478287084369286616501182716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143017855633962566947/25000000000000000000)
  centralHi := (572071422535850267789/100000000000000000000)
  directionLo := (143562687533150678583/25000000000000000000)
  directionHi := (574250750132602714333/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree133.table
  base := (17195981519083329974570433815299650664757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2278637670774587191000669353244913337000000000000)
      constant := (79524948132337876335223618127647192721060642563252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree133.table
  base := (13756785214989403914332615320077866730901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2283929824030794471670089548687664837000000000000)
      constant := (79885945108318752154455870236739272598616413860545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143562687533150678583/25000000000000000000)
  centralHi := (574250750132602714333/100000000000000000000)
  directionLo := (72052729777131199593/12500000000000000000)
  directionHi := (115284367643409919349/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree134.table
  base := (70569561542546071656257736509524859053421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2295766739449264711170383682073452177000000000000)
      constant := (80745688236523166790126007060404080869443830554789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree134.table
  base := (8821195192670526509497473268153633862477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2301098683331458512747092751166149177000000000000)
      constant := (81112133581205846350917059232111939649971160802344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72052729777131199593/12500000000000000000)
  centralHi := (115284367643409919349/20000000000000000000)
  directionLo := (57858477954331643629/10000000000000000000)
  directionHi := (578584779543316436291/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree135.table
  base := (72375974602310539498481282449678362768531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-256988423124882470148899778989110113000000000000)
      constant := (9108419433822265461983775693829802627426678814531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree135.table
  base := (14475194920260605451945304111054772086147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-257585282514680283758232883738292613000000000000)
      constant := (9149745491703564499422081749564843935104493940735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57858477954331643629/10000000000000000000)
  centralHi := (578584779543316436291/100000000000000000000)
  directionLo := (145184916284555380209/25000000000000000000)
  directionHi := (580739665138221520837/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree136.table
  base := (7420316525603817510560903541752328310917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-8062369815912179070968208787994913000000000000)
      constant := (287941896664293761383344794969707328594546660770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree136.table
  base := (74203165255179337545888286948453510958251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17377542)
      previous := (8688771)
      next := (8688771)
      square := (57860251434517460481232742744280000000000000)
      linear := (-8081094816376424203810031682086913000000000000)
      constant := (289248002216985917555306573951319927679804763731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145184916284555380209/25000000000000000000)
  centralHi := (580739665138221520837/100000000000000000000)
  directionLo := (582886584345976560519/100000000000000000000)
  directionHi := (14572164608649414013/2500000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree137.table
  base := (15210226700828198677523389969848655075817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2347153945473297271679526668559068697000000000000)
      constant := (84463987931276059579058011242231305530499949901765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree137.table
  base := (9506391687926116327103450052155296378559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2352605261233450635978102358601602197000000000000)
      constant := (84847023227347868636020851992379903706590995624248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582886584345976560519/100000000000000000000)
  centralHi := (14572164608649414013/2500000000000000000)
  directionLo := (5850256248714109359/1000000000000000000)
  directionHi := (585025624871410935901/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree138.table
  base := (77919879347029864325159971993085870526553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-262698112683108310205471221931956393000000000000)
      constant := (9524679365588579369512455571677171661120282024553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree138.table
  base := (77919879346405896000038262859739630143107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-263308235614901630783900617897787393000000000000)
      constant := (9567862353917813585839884647161032817258396205107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5850256248714109359/1000000000000000000)
  centralHi := (585025624871410935901/100000000000000000000)
  directionLo := (587156872821778705039/100000000000000000000)
  directionHi := (7339460910272233813/1250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree139.table
  base := (79809402785113119688338394752896744596947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2381412082822652312018955326216146377000000000000)
      constant := (86989587213055628789988045868126489941978856890523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree139.table
  base := (7980940278458131271540363994197774688913/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2386942979834778718132108763558570877000000000000)
      constant := (87383886514457634401272302139278424702208375222170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587156872821778705039/100000000000000000000)
  centralHi := (7339460910272233813/1250000000000000000)
  directionLo := (147320103186801188521/25000000000000000000)
  directionHi := (117856082549440950817/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree140.table
  base := (40859851909397712100764127789293353393783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2398541151497329832188669655044685217000000000000)
      constant := (88266406699562469294232263308104316424376457292094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree140.table
  base := (40859851909171094780627294368688788087713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2404111839135442759209111966037055217000000000000)
      constant := (88666399214951036026605093791928980478382890622834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147320103186801188521/25000000000000000000)
  centralHi := (117856082549440950817/20000000000000000000)
  directionLo := (147849081919955960951/25000000000000000000)
  directionHi := (118279265535964768761/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree141.table
  base := (16730156489695373713194992383731293227883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-268407802241334150262042664874802673000000000000)
      constant := (9950285861092086216083970505485624444339912529415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree141.table
  base := (83650782448090617168514064021750856027071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-269031188715122977809568352057282173000000000000)
      constant := (9995366587416846937893982274976811640579855713071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147849081919955960951/25000000000000000000)
  centralHi := (118279265535964768761/20000000000000000000)
  directionLo := (148376174792915953307/25000000000000000000)
  directionHi := (593504699171663813229/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree142.table
  base := (85602638674552248384765451995940078025591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2432799288846684872528098312701762897000000000000)
      constant := (90848085363865442734983200993028727595498860284319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree142.table
  base := (2675082458569471791752992517266962795697/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2438449557736770841363118370994023897000000000000)
      constant := (91259586729870334718802282871225593863688101736736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148376174792915953307/25000000000000000000)
  centralHi := (593504699171663813229/100000000000000000000)
  directionLo := (59560560733132184249/10000000000000000000)
  directionHi := (595605607331321842491/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree143.table
  base := (87575272497410498643840124987305208372649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2449928357521362392697812641530301737000000000000)
      constant := (92152944541683201940417116887428718179081751859841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree143.table
  base := (10946909062141252569588670926958355446131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2455618417037434882440121573472508237000000000000)
      constant := (92570261544317945298643766576255744102195902633432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59560560733132184249/10000000000000000000)
  centralHi := (595605607331321842491/100000000000000000000)
  directionLo := (597699130859480442349/100000000000000000000)
  directionHi := (11953982617189608847/2000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree144.table
  base := (44784341958717129072746537279660351359109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-274117491799559990318614107817648953000000000000)
      constant := (10385238920365845788845748297094748385854759106218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree144.table
  base := (89568683917195267202751466457114008665327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-274754141815344324835236086216776953000000000000)
      constant := (10432258192233894108780125135656585459681901247327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597699130859480442349/100000000000000000000)
  centralHi := (11953982617189608847/2000000000000000000)
  directionLo := (299892673541653860093/50000000000000000000)
  directionHi := (599785347083307720187/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree145.table
  base := (91582872934999542300710030710714098827483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2484186494870717433037241299187379417000000000000)
      constant := (94790702588704048985201933284757237141972455349347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree145.table
  base := (91582872934795911695966725846584540933033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2489956135638762964594127978429476917000000000000)
      constant := (95219773287242044754921653974362890813016980999297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299892673541653860093/50000000000000000000)
  centralHi := (599785347083307720187/100000000000000000000)
  directionLo := (60186433198978446477/10000000000000000000)
  directionHi := (601864331989784464771/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree146.table
  base := (5851114971904719129785430570669457342169/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2501315563545394953206955628015918257000000000000)
      constant := (96123601457927699062671599689473784447798839448336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree146.table
  base := (4680891977515100612055451427965652899813/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2507124994939427005671131180907961257000000000000)
      constant := (96558610215739150015777852326220179945666320406340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60186433198978446477/10000000000000000000)
  centralHi := (601864331989784464771/100000000000000000000)
  directionLo := (150984040064499672047/25000000000000000000)
  directionHi := (603936160257998688189/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree147.table
  base := (95673583764224281760257816987877443449919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-279827181357785830375185550760495233000000000000)
      constant := (10829538543441506112623640035733251872994895103919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree147.table
  base := (2391839594101911786379065240215238653973/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-280477094915565671860903820376271733000000000000)
      constant := (10878537168400708522185434201144058601882794878920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150984040064499672047/25000000000000000000)
  centralHi := (603936160257998688189/100000000000000000000)
  directionLo := (303000452645223228561/50000000000000000000)
  directionHi := (606000905290446457123/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree148.table
  base := (97750105576600878622950341582910680439081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2535573700894749993546384285672995937000000000000)
      constant := (98817438887851412967049095369976896308232125065729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree148.table
  base := (19550021115294991109564398812769584041613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2541462713540755087825137585864929937000000000000)
      constant := (99264446186853539063186127038606962655852627482585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303000452645223228561/50000000000000000000)
  centralHi := (606000905290446457123/100000000000000000000)
  directionLo := (304029319621688065707/50000000000000000000)
  directionHi := (121611727848675226283/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree149.table
  base := (99847404987953133612953874820620415156117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2552702769569427513716098614501534777000000000000)
      constant := (100178377448570871138862787281492690161901628903053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree149.table
  base := (9984740498784586167186842191745346758149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2558631572841419128902140788343414277000000000000)
      constant := (100631445229490250780498929922533628975774843293410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304029319621688065707/50000000000000000000)
  centralHi := (121611727848675226283/20000000000000000000)
  directionLo := (152527358264052875089/25000000000000000000)
  directionHi := (610109433056211500357/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree150.table
  base := (50982740999310851968247937482763930681783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-285536870916011670431756993703341513000000000000)
      constant := (11283184730349036625229821266171663463468554719566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree150.table
  base := (20393096399706064943926863587455388803509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-286200048015787018886571554535766513000000000000)
      constant := (11334203515947325014544061269123602560134736987545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152527358264052875089/25000000000000000000)
  centralHi := (610109433056211500357/100000000000000000000)
  directionLo := (12243067129601755229/2000000000000000000)
  directionHi := (612153356480087761451/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree151.table
  base := (52052168304470046922340988477928679879871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2586960906918782554055527272158612457000000000000)
      constant := (102928294261571991150972454862569816237426558585678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree151.table
  base := (20820867321772451248224534913075567590487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2592969291442747211056147193300382957000000000000)
      constant := (103393605428969776072694978060816466354610032961915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12243067129601755229/2000000000000000000)
  centralHi := (612153356480087761451/100000000000000000000)
  directionLo := (307095239052766408897/50000000000000000000)
  directionHi := (122838095621106563559/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree152.table
  base := (106263968819234709178394997275249217467921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2604089975593460074225241600987151297000000000000)
      constant := (104317272513871862556285950688562144348052769285289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree152.table
  base := (2125279376383368186809394803349306846563/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2610138150743411252133150395778867297000000000000)
      constant := (104788766585830820033990523413275373677391052053350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307095239052766408897/50000000000000000000)
  centralHi := (122838095621106563559/20000000000000000000)
  directionLo := (616220865389324974553/100000000000000000000)
  directionHi := (308110432694662487277/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree153.table
  base := (108444378629824934264009602239468871613731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-1007773565654801074354077635453937000000000000)
      constant := (40644212737427818891574517629070043758950072179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree153.table
  base := (27111094657442116101018133365482600200607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6428916826057495609025860304920000000000000)
      linear := (-1010114190712831715959305497215437000000000000)
      constant := (40827879705543205797094406109795306872112958652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616220865389324974553/100000000000000000000)
  centralHi := (308110432694662487277/50000000000000000000)
  directionLo := (61824458468055678799/10000000000000000000)
  directionHi := (618244584680556787991/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree154.table
  base := (22129113208204645326303382533887702651709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2638348112942815114564670258644228977000000000000)
      constant := (107123268710114296248965256614369548972802910056905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree154.table
  base := (110645566040975131354403103987604056677647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2644475869344739334287156800735835977000000000000)
      constant := (107607251013839579725866141732946074503899501416823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61824458468055678799/10000000000000000000)
  centralHi := (618244584680556787991/100000000000000000000)
  directionLo := (620261701245933558503/100000000000000000000)
  directionHi := (77532712655741694813/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree155.table
  base := (112867531053135225768053397686001033693111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2655477181617492634734384587472767817000000000000)
      constant := (108540286654073914310984558585186000645237008171999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree155.table
  base := (112867531053094264832447795148469349456171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2661644728645403375364160003214320317000000000000)
      constant := (109030574285004364132577366666147416293867727679539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620261701245933558503/100000000000000000000)
  centralHi := (77532712655741694813/12500000000000000000)
  directionLo := (124454455858866751693/20000000000000000000)
  directionHi := (311136139647166879233/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree156.table
  base := (57555136833229936372567618331308528559519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-296956250032463350544899879589034073000000000000)
      constant := (12218516795770762233962345929215269517744027627038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree156.table
  base := (57555136833212494654631705367933837176739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-297645954216229712937907022854756073000000000000)
      constant := (12273698325291165060191409641612347458435437901478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124454455858866751693/20000000000000000000)
  centralHi := (311136139647166879233/50000000000000000000)
  directionLo := (39017273875041096437/6250000000000000000)
  directionHi := (624276382000657542993/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree157.table
  base := (117373793881289538085068179461772909180359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2689735318966847675073813245129845497000000000000)
      constant := (111402362233711201307818760510081020448379008869231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree157.table
  base := (58686896940629915815300841465788369866557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2695982447246731457518166408171288997000000000000)
      constant := (111905382941696015941716516967626770720636205314026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39017273875041096437/6250000000000000000)
  centralHi := (624276382000657542993/100000000000000000000)
  directionLo := (78284258941123550497/12500000000000000000)
  directionHi := (626274071528988403977/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree158.table
  base := (11965809169791015567622303743932016785721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2706864387641525195243527573958384337000000000000)
      constant := (112847419869404827979746609190507455656733363454890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree158.table
  base := (59829045848942429461260311727535220251973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2713151306547395498595169610649773337000000000000)
      constant := (113356868327238849071409906155403615209399850459514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78284258941123550497/12500000000000000000)
  centralHi := (626274071528988403977/100000000000000000000)
  directionLo := (125653081811018398359/20000000000000000000)
  directionHi := (157066352263772997949/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree159.table
  base := (121963167116601360920987098519472123666127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-302665939590689190601471322531880353000000000000)
      constant := (12700202674336161820361650316520340460132469048127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree159.table
  base := (121963167116579820142722651795395280867887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-303368907316451059963574757014250853000000000000)
      constant := (12757526787139633814006603946727131692286222409887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125653081811018398359/20000000000000000000)
  centralHi := (157066352263772997949/25000000000000000000)
  directionLo := (630250454788275142279/100000000000000000000)
  directionHi := (15756261369706878557/2500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree160.table
  base := (62144510068818315807545132230763130646147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2741122524990880235582956231615462017000000000000)
      constant := (115765574832580632867100162555323016527835912266646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree160.table
  base := (124289020137618289862473523182049113289699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2747489025148723580749176015606742017000000000000)
      constant := (116288001212757130724846783454243041590557973813291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630250454788275142279/100000000000000000000)
  centralHi := (15756261369706878557/2500000000000000000)
  directionLo := (316114633996313603089/50000000000000000000)
  directionHi := (632229267992627206179/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree161.table
  base := (63317825380641715160927099027807447616911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2758251593665557755752670560444000857000000000000)
      constant := (117238672160077737795661999343353189014116141372398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree161.table
  base := (126635650761267813116188334434813285418051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2764657884449387621826179218085226357000000000000)
      constant := (117767648712747510907859505447881102174395268056459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316114633996313603089/50000000000000000000)
  centralHi := (632229267992627206179/100000000000000000000)
  directionLo := (634201907007664882043/100000000000000000000)
  directionHi := (158550476751916220511/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree162.table
  base := (64501529493901673613749025123278990835299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-308375629148915030658042765474726633000000000000)
      constant := (13191235116835998832321467348879700219360035138598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree162.table
  base := (129003058987790050367582021176112682207343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-309091860416672406989242491173745633000000000000)
      constant := (13250742620470562792920921734273108873260395845343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634201907007664882043/100000000000000000000)
  centralHi := (158550476751916220511/25000000000000000000)
  directionLo := (127233685853680179757/20000000000000000000)
  directionHi := (318084214634200449393/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree163.table
  base := (131391244817452242650530536306634841585181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2792509731014912796092099218101078537000000000000)
      constant := (120212906506926448164725455300817068441915058780629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree163.table
  base := (26278248963488184363795684322904357870243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2798995603050715703980185623042195037000000000000)
      constant := (120755105827226855274499359748415622880803530870935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127233685853680179757/20000000000000000000)
  centralHi := (318084214634200449393/50000000000000000000)
  directionLo := (127625778264971215809/20000000000000000000)
  directionHi := (319064445662428039523/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree164.table
  base := (33450052062620097133756358458950409978987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2809638799689590316261813546929617377000000000000)
      constant := (121714043526292019823435966141809677232055428355532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree164.table
  base := (13380020825047075043928486654268951629451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2816164462351379745057188825520679377000000000000)
      constant := (122262915441729788736749633473812362379836355590590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127625778264971215809/20000000000000000000)
  centralHi := (319064445662428039523/50000000000000000000)
  directionLo := (640083348861033536819/100000000000000000000)
  directionHi := (32004167443051676841/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree165.table
  base := (27245989857426521677783490130735333850099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-314085318707140870714614208417572913000000000000)
      constant := (13691614123291940014345122284653560654098686920495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree165.table
  base := (136229949287124403210773682914439179661841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-314814813516893754014910225333240413000000000000)
      constant := (13753345825305624709416860246118104615532384167841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640083348861033536819/100000000000000000000)
  centralHi := (32004167443051676841/5000000000000000000)
  directionLo := (642031856713373020627/100000000000000000000)
  directionHi := (160507964178343255157/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree166.table
  base := (138680467927648415238342813198595956504777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2843896937038945356601242204586695057000000000000)
      constant := (124744357256939378206334678828599656678156425080993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree166.table
  base := (138680467927641430198975294953488484431541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2850502180952707827211195230477648057000000000000)
      constant := (125306696785295966365169883087970444725300302237869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642031856713373020627/100000000000000000000)
  centralHi := (160507964178343255157/25000000000000000000)
  directionLo := (128794893777740541/20000000000000000)
  directionHi := (643974468888702705001/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree167.table
  base := (35287941043065536815211059988414776916899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2861026005713622876770956533415233897000000000000)
      constant := (126273533968234240384901858313669626481411613032364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree167.table
  base := (141151764172256201136896910771359434738527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2867671040253371868288198432956132397000000000000)
      constant := (126842668514372287878525984590229083122159826684743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128794893777740541/20000000000000000)
  centralHi := (643974468888702705001/100000000000000000000)
  directionLo := (645911238581705056567/100000000000000000000)
  directionHi := (80738904822713132071/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree168.table
  base := (2872876760424062016736071421211779254007/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-319795008265366710771185651360419193000000000000)
      constant := (14201339693724263763465729215266579624228235800350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree168.table
  base := (143643838021198039287154078863081559943027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1857956962730616231008473628121880000000000000)
      linear := (-320537766617115101040577959492735193000000000000)
      constant := (14265336401665101652554729947838959779866880725027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell086.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645911238581705056567/100000000000000000000)
  centralHi := (80738904822713132071/12500000000000000000)
  directionLo := (64784221819191275481/10000000000000000000)
  directionHi := (647842218191912754811/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree169.table
  base := (146156689474695660822157924782598285380321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2895284143062977917110385191072311577000000000000)
      constant := (129359927082797970342937985244577584460669146096889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 10787
  qDenominator := 21012
  table := BinomialMassData.Q10787_21012.Degree169.table
  base := (29231337894938270481147163114470638326161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (5022109638)
      previous := (2511054819)
      next := (2511054819)
      square := (16721612664575546079076262653096920000000000000)
      linear := (-2902008758854699950442204837913101077000000000000)
      constant := (129942774087143039658208068629824268270289157847245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10787_21012.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell086.Kernel169
