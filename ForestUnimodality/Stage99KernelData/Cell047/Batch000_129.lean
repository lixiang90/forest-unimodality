import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell047.Parameters
import ForestUnimodality.BinomialMassData.Q47_97.Batch000_049
import ForestUnimodality.BinomialMassData.Q47_97.Batch050_099
import ForestUnimodality.BinomialMassData.Q47_97.Batch100_149
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree000.table
  base := (215650760179384863151028639/4000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (450106742213159938259536830000000000000)
      linear := (13506966466709027785420005500000000000)
      constant := (269563450224231078938785798750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree000.table
  base := (215650760179384863151028639/4000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (450106742213159938259536830000000000000)
      linear := (13506966466709027785420005500000000000)
      constant := (269563450224231078938785798750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree001.table
  base := (322655778296280229067871810743546922794041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-7953972456028654149234879968381000000000000)
      constant := (3037733633056554962991489041390823996569131769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree001.table
  base := (161034676338677279730126556238594416583219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-9575485900284138670988318133953765500000000000)
      constant := (3640187827055717524221138437684506870381249677971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49976081004292051691/100000000000000000000)
  directionHi := (12494020251073012923/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree002.table
  base := (198761776750103708113557390458450586891393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-16162119007027838783335793600261000000000000)
      constant := (1877857530749629846238689102463023572061116737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree002.table
  base := (99046000885598999081269150804496277427089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-19456107801580399189058309680938080500000000000)
      constant := (2246853617014612891405133007274434193571864442801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/100000000000000000000)
  centralHi := (12494020251073012923/25000000000000000000)
  directionLo := (17669212887631557023/25000000000000000000)
  directionHi := (70676851550526228093/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree003.table
  base := (15848665297752234192552902900491061428169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-12185132779013511708718353616070500000000000)
      constant := (605244204507777739430437715864888087910568484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree003.table
  base := (63103686902959357909431448414744654016589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-29336729702876659707128301227922395500000000000)
      constant := (1446733503810334630246761202425394086840648248301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/25000000000000000000)
  centralHi := (70676851550526228093/100000000000000000000)
  directionLo := (43280555731305838149/50000000000000000000)
  directionHi := (86561111462611676299/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree004.table
  base := (21028286022872685807316458334567376757949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-16289206054513104025768810432010500000000000)
      constant := (411372546034713220549231263439110895831084282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree004.table
  base := (83654823808349057836520868080005435207211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-78434703208345840450396585549813421000000000000)
      constant := (1965469039451130238079332786865005975815020565899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43280555731305838149/50000000000000000000)
  centralHi := (86561111462611676299/100000000000000000000)
  directionLo := (49976081004292051691/50000000000000000000)
  directionHi := (99952162008584103383/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree005.table
  base := (58113458739818637617672731322703302210533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-40786558660025392685638534495901000000000000)
      constant := (595888040359179811948711273838070370498904997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree005.table
  base := (7220765440396736479063311629620244598837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-49097973505469180743268284321891025500000000000)
      constant := (711762635495365131033511720264024076758112226132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/50000000000000000000)
  centralHi := (99952162008584103383/100000000000000000000)
  directionLo := (22349982874926597339/20000000000000000000)
  directionHi := (13968739296829123337/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree006.table
  base := (41706840060690907236815191700606033947947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-48994705211024577319739448127781000000000000)
      constant := (463269296145098690559412194787948173416233323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree006.table
  base := (2072278061331304735821053184807976091077/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-58978595406765441261338275868875340500000000000)
      constant := (553668207413220370408644669864337565703053266930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22349982874926597339/20000000000000000000)
  centralHi := (13968739296829123337/12500000000000000000)
  directionLo := (61207948902257305333/50000000000000000000)
  directionHi := (122415897804514610667/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree007.table
  base := (3863584278209520107293046498165559439517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-28601425881011880976920180879830500000000000)
      constant := (193698813957736058431515515385467495065661812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree007.table
  base := (30709704163122925602775750289826751468171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-2810580298288232725690133363912639000000000000)
      constant := (18916585831142799484518048199667260823637026011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61207948902257305333/50000000000000000000)
  centralHi := (122415897804514610667/100000000000000000000)
  directionLo := (33056070459743969243/25000000000000000000)
  directionHi := (132224281838975876973/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree008.table
  base := (23459298247728503556452262878988444494729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-65410998313022946587941275391541000000000000)
      constant := (347011866625185265502640222303370274250905161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree008.table
  base := (4660786935596507087785289195019451624329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-157479678418715924594956517925687941000000000000)
      constant := (831320055960923019754384015208953952101405289805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33056070459743969243/25000000000000000000)
  centralHi := (132224281838975876973/100000000000000000000)
  directionLo := (17669212887631557023/12500000000000000000)
  directionHi := (28270740620210491237/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree009.table
  base := (18065013509161861919990832922971553860697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-73619144864022131222042189023421000000000000)
      constant := (329939601980429871752747941391038350275298073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree009.table
  base := (17939768722399882195522483507835628015931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-177240922221308445631096501019656571000000000000)
      constant := (791450310788307132125849112136181317028549364379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/12500000000000000000)
  centralHi := (28270740620210491237/20000000000000000000)
  directionLo := (74964121506438077537/50000000000000000000)
  directionHi := (5997129720515046203/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree010.table
  base := (13975846446940363284846038911670081363557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-81827291415021315856143102655301000000000000)
      constant := (329124332726601409716705155512413795549707813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree010.table
  base := (13871458969622858544806520505632002802907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-197002166023900966667236484113625201000000000000)
      constant := (790456285637766714445447580988275323508497263163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/50000000000000000000)
  centralHi := (5997129720515046203/4000000000000000000)
  directionLo := (79019122251319029157/50000000000000000000)
  directionHi := (31607648900527611663/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree011.table
  base := (134372371648449279968978865971359123317/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-45017718983010250245122008143590500000000000)
      constant := (170203605951684686712167197895031219651586120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree011.table
  base := (5330041022484251468298948054859937198151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-108381704913246743851688233603796915500000000000)
      constant := (409211129300764305093197080339447029232864024359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79019122251319029157/50000000000000000000)
  centralHi := (31607648900527611663/20000000000000000000)
  directionLo := (5179747161988893959/3125000000000000000)
  directionHi := (165751909183644606689/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree012.table
  base := (2030180929924291609348479723241187040353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-49121792258509842562172464959530500000000000)
      constant := (180642159888891925733240561246738657725362754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree012.table
  base := (1608328382431849578535936301442506667239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-236524653629086008739516450301562461000000000000)
      constant := (869384292848081965950182908443754552510781270755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/3125000000000000000)
  centralHi := (165751909183644606689/100000000000000000000)
  directionLo := (173122222925223352597/100000000000000000000)
  directionHi := (86561111462611676299/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree013.table
  base := (1184817904817957339137161899345298394463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-106451731068018869758445843550941000000000000)
      constant := (390207321788514077742167904447622562967511835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree013.table
  base := (5852990394017076553469224907206845220071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-256285897431678529775656433395531091000000000000)
      constant := (939656706438464608259830401430697978228230941639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173122222925223352597/100000000000000000000)
  centralHi := (86561111462611676299/50000000000000000000)
  directionLo := (90095661303858426973/50000000000000000000)
  directionHi := (180191322607716853947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree014.table
  base := (4054813622202482114384358665066910096973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-114659877619018054392546757182821000000000000)
      constant := (426187581159051972416582204265768557102418957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree014.table
  base := (3989969443719751825544587194014948678081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-5633615127230021445138702377336729000000000000)
      constant := (20956866612234550153830770862852404453491142321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90095661303858426973/50000000000000000000)
  centralHi := (180191322607716853947/100000000000000000000)
  directionLo := (186993372651722210291/100000000000000000000)
  directionHi := (46748343162930552573/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree015.table
  base := (610826089500219394371444874615606169317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-61434012085008619513323835407350500000000000)
      constant := (234285154998885050011622195505148976894207306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree015.table
  base := (595893145849571318271212888537379573797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-147904192518431785923968199791734175500000000000)
      constant := (564757319784285197604644383434610291326128382346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/100000000000000000000)
  centralHi := (46748343162930552573/25000000000000000000)
  directionLo := (12097283089895997111/6250000000000000000)
  directionHi := (193556529438335953777/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree016.table
  base := (520809795446833375777650266282546945443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-65538085360508211830374292223290500000000000)
      constant := (258452210351922429635433349986580484209673187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree016.table
  base := (986228396830063181925308758219851576531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-315569628839456092884076382677436981000000000000)
      constant := (1246466546853669108854355011515507846944076009779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097283089895997111/6250000000000000000)
  centralHi := (193556529438335953777/100000000000000000000)
  directionLo := (39980864803433641353/20000000000000000000)
  directionHi := (99952162008584103383/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree017.table
  base := (-92304126940503966227111302957104229949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-69642158636007804147424749039230500000000000)
      constant := (285433274383170966146142274873040106300409859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree017.table
  base := (-236196687817018712327353505644285372259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-335330872642048613920216365771405611000000000000)
      constant := (1376971074026327884547058808241358350356728580669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39980864803433641353/20000000000000000000)
  centralHi := (99952162008584103383/50000000000000000000)
  directionLo := (103028330367560230571/50000000000000000000)
  directionHi := (206056660735120461143/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree018.table
  base := (-630481897282681539331735912786752166811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-73746231911507396464475205855170500000000000)
      constant := (315107984256110151529663222125528448862475301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree018.table
  base := (-1309139389952369906643120439085373786917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-355092116444641134956356348865374241000000000000)
      constant := (1520453579929438277656665748626599984511393970747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103028330367560230571/50000000000000000000)
  centralHi := (206056660735120461143/100000000000000000000)
  directionLo := (53007638662894671069/25000000000000000000)
  directionHi := (212030554651578684277/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree019.table
  base := (-68973432137597889366680519927282412961/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-77850305187006988781525662671110500000000000)
      constant := (347383648161106840252510967058321696423199216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree019.table
  base := (-2252208422910101024735579541366814309583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-374853360247233655992496331959342871000000000000)
      constant := (1676471083943590975075866564053085772130881660753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/25000000000000000000)
  centralHi := (212030554651578684277/100000000000000000000)
  directionLo := (13615042918244484239/6250000000000000000)
  directionHi := (8713627467676469913/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree020.table
  base := (-3038786605099514455543446777858111058751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-163908756925013162197152238974101000000000000)
      constant := (764373561266845853073096003040153033048211841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree020.table
  base := (-770240865086589494595119039664424937877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-197307302024913088514318157526655750500000000000)
      constant := (922336038670591460803211092711900810997192504214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13615042918244484239/6250000000000000000)
  centralHi := (8713627467676469913/4000000000000000000)
  directionLo := (223499828749265973391/100000000000000000000)
  directionHi := (13968739296829123337/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree021.table
  base := (-3768559002942256703370276770395872243507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-172116903476012346831253152605981000000000000)
      constant := (838915411326307403244401882342756238060842637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree021.table
  base := (-3808049660303516127544458303499364307977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-8456649956171810164587271390760819000000000000)
      constant := (41321854964144334553264241383420288580085975943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223499828749265973391/100000000000000000000)
  centralHi := (13968739296829123337/6250000000000000000)
  directionLo := (45803834827882600671/20000000000000000000)
  directionHi := (57254793534853250839/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree022.table
  base := (-176278821102100527760995846863471473033/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-180325050027011531465354066237861000000000000)
      constant := (918294019016208893119402358529221922755812575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree022.table
  base := (-4443943823644751525943297825075173631559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-434137091655011219100916281241248761000000000000)
      constant := (2216530850146668171588366005857615271312887946969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/20000000000000000000)
  centralHi := (57254793534853250839/25000000000000000000)
  directionLo := (58602149489185942003/25000000000000000000)
  directionHi := (234408597956743768013/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree023.table
  base := (-4962854959500880099489177944908177897013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-188533196578010716099454979869741000000000000)
      constant := (1002426267295161583315919988886191954167004683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree023.table
  base := (-2498730596004667078883123852491617234977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-226949167728801870068528132167608695500000000000)
      constant := (1209876401424380167037713723911652675370079478207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58602149489185942003/25000000000000000000)
  centralHi := (234408597956743768013/100000000000000000000)
  directionLo := (119838432346006908471/50000000000000000000)
  directionHi := (239676864692013816943/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree024.table
  base := (-2721867404206417860258854601529425802363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-98370671564504950366777946750810500000000000)
      constant := (545620688435049674251077431635141632625566533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree024.table
  base := (-2738055448870646571139433244830148026729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-236829789630098130586598123714593010500000000000)
      constant := (1317133556236491363820770923586042429456832920439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119838432346006908471/50000000000000000000)
  centralHi := (239676864692013816943/100000000000000000000)
  directionLo := (244831795609029221333/100000000000000000000)
  directionHi := (122415897804514610667/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree025.table
  base := (-5856080222225591735503854231120872115317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-204949489680009085367656807133501000000000000)
      constant := (1184678470119080963996103817123158714266982347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree025.table
  base := (-1177270600763886987458826448646773406071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-493420823062788782209336230523154651000000000000)
      constant := (2859927839678440568788998096140446670812446921805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/100000000000000000000)
  centralHi := (122415897804514610667/50000000000000000000)
  directionLo := (249880405021460258457/100000000000000000000)
  directionHi := (124940202510730129229/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree026.table
  base := (-620550131503900622340840685114192878269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-106578818115504135000878860382690500000000000)
      constant := (641342380739270432566412370686585796041834895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree026.table
  base := (-779223707539712392537923217792577794181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-256591033432690651622738106808561640500000000000)
      constant := (1548304213121197068702706468910662336423827525484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249880405021460258457/100000000000000000000)
  centralHi := (124940202510730129229/50000000000000000000)
  directionLo := (254829012253778871009/100000000000000000000)
  directionHi := (25482901225377887101/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree027.table
  base := (-1299378930568366816688435910588459539357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-221365782782007454635858634397261000000000000)
      constant := (1385214179159090857065643101303602920970949935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree027.table
  base := (-3261655424793900255401081745510392500649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-266471655333986912140808098355545955500000000000)
      constant := (1672099201264763002096794935796058825674305935159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254829012253778871009/100000000000000000000)
  centralHi := (25482901225377887101/10000000000000000000)
  directionLo := (8115104199619844653/3125000000000000000)
  directionHi := (259683334387835028897/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree028.table
  base := (-6734557286261847554482138689511225615579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-229573929333006639269959548029141000000000000)
      constant := (1492226292211374230798965520499176878183017189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree028.table
  base := (-6759207946406846955744387585757635815239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-11279684785113598884035840404184909000000000000)
      constant := (73522465756196411253746156750732100826106396201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8115104199619844653/3125000000000000000)
  centralHi := (259683334387835028897/100000000000000000000)
  directionLo := (52889712735590350789/20000000000000000000)
  directionHi := (132224281838975876973/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree029.table
  base := (-1730569302419604908290861107751444863133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-118891037942002911952030230830510500000000000)
      constant := (801842729698137732903725888459442810565563206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree029.table
  base := (-3472631936463534965580660296820811957169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-286232899136579433176948081449514585500000000000)
      constant := (1935865112393150609466021504234043550188287506479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52889712735590350789/20000000000000000000)
  centralHi := (132224281838975876973/50000000000000000000)
  directionLo := (6728235815570418927/2500000000000000000)
  directionHi := (269129432622816757081/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree030.table
  base := (-7063406295120523486589472229736224980929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-245990222435005008538161375292901000000000000)
      constant := (1719560142949873953561826210931941859154439039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree030.table
  base := (-3542412917873037226346955999280109354037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-296113521037875693695018072996498900500000000000)
      constant := (2075755496976592926201122012039856477311965946667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6728235815570418927/2500000000000000000)
  centralHi := (269129432622816757081/100000000000000000000)
  directionLo := (273730269017561931339/100000000000000000000)
  directionHi := (13686513450878096567/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree031.table
  base := (-223778747747831505117039732691590931247/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-127099184493002096586131144462390500000000000)
      constant := (919911173735741295480094246553037634846351632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree031.table
  base := (-7180864834186603055400248550888298351883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-611988285878343908426176129086966431000000000000)
      constant := (4441876011681838981329984674320250877437925980053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273730269017561931339/100000000000000000000)
  centralHi := (13686513450878096567/5000000000000000000)
  directionLo := (139127521404801848631/50000000000000000000)
  directionHi := (278255042809603697263/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree032.table
  base := (-1443493273777328132087648607599878981717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-262406515537003377806363202556661000000000000)
      constant := (1964447155475441486538986787829255693305123735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree032.table
  base := (-7236024940647623976974241947209435613799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-631749529680936429462316112180935061000000000000)
      constant := (4742765545708898862666807660806976107163746266809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139127521404801848631/50000000000000000000)
  centralHi := (278255042809603697263/100000000000000000000)
  directionLo := (17669212887631557023/6250000000000000000)
  directionHi := (282707406202104912369/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree033.table
  base := (-723540805350845472500853062102063511843/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-135307331044001281220232058094270500000000000)
      constant := (1046706169402972262280044341910779922085346065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree033.table
  base := (-7252664548492655575278212258519573924547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-651510773483528950498456095274903691000000000000)
      constant := (5054126317548664712918580090055138646794393402077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/6250000000000000000)
  centralHi := (282707406202104912369/100000000000000000000)
  directionLo := (71772682039403712427/25000000000000000000)
  directionHi := (287090728157614849709/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree034.table
  base := (-3608428237390194738418048521966253582897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-139411404319500873537282514910210500000000000)
      constant := (1113349015212751029124624055319606520038522127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree034.table
  base := (-226027850741528914999692394398109332141/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-335636008643060735767298039184436160500000000000)
      constant := (2687955357579249581578199730832588905663898875696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71772682039403712427/25000000000000000000)
  centralHi := (287090728157614849709/100000000000000000000)
  directionLo := (58281624845783793149/20000000000000000000)
  directionHi := (145704062114459482873/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree035.table
  base := (-3581850947658713213850360652363448497281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-143515477595000465854332971726150500000000000)
      constant := (1182143222426584863281064563845054813089083071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree035.table
  base := (-7178591399835077566972919761810466846151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-14102719614055387603484409417608999000000000000)
      constant := (116491349430667515402413223829032043054783696809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58281624845783793149/20000000000000000000)
  centralHi := (145704062114459482873/50000000000000000000)
  directionLo := (73915620617010240663/25000000000000000000)
  directionHi := (295662482468040962653/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree036.table
  base := (-7077638845663921676751408034558684721851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-295239101741000116342766857084181000000000000)
      constant := (2506161638251055682961838750399713335452103941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree036.table
  base := (-354572793393745811967761327437449950087/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-355397252445653256803438022278404790500000000000)
      constant := (3025292170852576238156705178149010762905350322170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73915620617010240663/25000000000000000000)
  centralHi := (295662482468040962653/100000000000000000000)
  directionLo := (74964121506438077537/25000000000000000000)
  directionHi := (299856486025752310149/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree037.table
  base := (-6960188152636394190659403769939125586527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-303447248291999300976867770716061000000000000)
      constant := (2652309301159643300490967220105989767356367457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree037.table
  base := (-1394600360529534280430592152936308506393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-730555748693899034643016027650778211000000000000)
      constant := (6403401099456287847446401852003968437526495897315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/25000000000000000000)
  centralHi := (299856486025752310149/100000000000000000000)
  directionLo := (15199631647202815627/5000000000000000000)
  directionHi := (303992632944056312541/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree038.table
  base := (-681271608283291382496034971710924932771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-155827697421499242805484342173970500000000000)
      constant := (1401358289188255669939389844349708536537788305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree038.table
  base := (-272983676311004026627927017535996459769/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-750316992496491555679156010744746841000000000000)
      constant := (6766495610506330909346392551778497714334759576975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15199631647202815627/5000000000000000000)
  centralHi := (303992632944056312541/100000000000000000000)
  directionLo := (308073253556369791113/100000000000000000000)
  directionHi := (154036626778184895557/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree039.table
  base := (-6636451066422131618953301354903765607659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-319863541393997670245069597979821000000000000)
      constant := (2957371911602202963496511343179639469397536469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree039.table
  base := (-3323725571633700020909308254825417377721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-385039118149542038357647996919357735500000000000)
      constant := (3569920100886333341909208870323538773341148489511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308073253556369791113/100000000000000000000)
  centralHi := (154036626778184895557/50000000000000000000)
  directionLo := (78025131459900018307/25000000000000000000)
  directionHi := (312100525839600073229/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree040.table
  base := (-6432498374614490834221741262649921372913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-328071687944996854879170511611701000000000000)
      constant := (3116264901339899110695923195957766889802261583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree040.table
  base := (-1610670351965536009497239517306902817267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-394919740050838298875717988466342050500000000000)
      constant := (3761704990125498768262973244476264850385991695194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78025131459900018307/25000000000000000000)
  centralHi := (312100525839600073229/100000000000000000000)
  directionLo := (316076489005276116629/100000000000000000000)
  directionHi := (31607648900527611663/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree041.table
  base := (-3100926526718652490168502554075061432437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-168139917247998019756635712621790500000000000)
      constant := (1639693092600764394332729274867723246982200267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree041.table
  base := (-248450979119393309266825102436753179267/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-809600723904269118787575960026652731000000000000)
      constant := (7917182540711169007389546992159379180910014739925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316076489005276116629/100000000000000000000)
  centralHi := (31607648900527611663/10000000000000000000)
  directionLo := (32000305557048981823/10000000000000000000)
  directionHi := (320003055570489818231/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree042.table
  base := (-5945411361310165605888349659920433725129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-344487981046995224147372338875461000000000000)
      constant := (3446727330291622060524441087577710639080261239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree042.table
  base := (-5954123450300402843181422010466796268201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-16925754442997176322932978431033089000000000000)
      constant := (169819136881599706958695702342834863281712342759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32000305557048981823/10000000000000000000)
  centralHi := (320003055570489818231/100000000000000000000)
  directionLo := (20242626381965216751/6250000000000000000)
  directionHi := (323882022111443468017/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree043.table
  base := (-5663980914616067185425134920389120807381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-352696127597994408781473252507341000000000000)
      constant := (3618280737747631331261835881221711762323352171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree043.table
  base := (-1418008222926423992385010151212740816329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-424561605754727080429927963107294995500000000000)
      constant := (4367628651867319893347874975184885792857288428078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20242626381965216751/6250000000000000000)
  centralHi := (323882022111443468017/100000000000000000000)
  directionLo := (327715078871182118173/100000000000000000000)
  directionHi := (163857539435591059087/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree044.table
  base := (-1339572427792039259356096748255126480237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-180452137074496796707787083069610500000000000)
      constant := (1897019778919066348879046296029977029894900134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree044.table
  base := (-536572786645162452811098915660197166461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-434442227656023340947997954654279310500000000000)
      constant := (4579762475193456751934817645890268503853525254255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327715078871182118173/100000000000000000000)
  centralHi := (163857539435591059087/50000000000000000000)
  directionLo := (5179747161988893959/1562500000000000000)
  directionHi := (331503818367289213377/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree045.table
  base := (-5028994174087131100609057385171898291231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-369112420699992778049675079771101000000000000)
      constant := (3973997614277983531925766969359712608977807521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree045.table
  base := (-1258965495699352116934406834938586359921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-444322849557319601466067946201263625500000000000)
      constant := (4796962940742570140150222780522426784691494899422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/1562500000000000000)
  centralHi := (331503818367289213377/100000000000000000000)
  directionLo := (335249743123898960087/100000000000000000000)
  directionHi := (41906217890487370011/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree046.table
  base := (-4676686336559355169361134058232887426709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-377320567250991962683775993402981000000000000)
      constant := (4158149336626933318005518888392272762202095019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree046.table
  base := (-4683024579625679196368722013567992631887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-908406942917231723968275875496495881000000000000)
      constant := (10038446783269318539907527494506278954841107096017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335249743123898960087/100000000000000000000)
  centralHi := (41906217890487370011/12500000000000000000)
  directionLo := (16947713631725357227/5000000000000000000)
  directionHi := (338954272634507144541/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree047.table
  base := (-4301900270054709531587689159747687961277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-385528713801991147317876907034861000000000000)
      constant := (4346489699806521952368430707321391003972344707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree047.table
  base := (-4307747155606771975276378435805689864917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-928168186719824245004415858590464511000000000000)
      constant := (10493075648648203250770465610837746957510451268747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16947713631725357227/5000000000000000000)
  centralHi := (338954272634507144541/100000000000000000000)
  directionLo := (85654687411772509399/25000000000000000000)
  directionHi := (342618749647090037597/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree048.table
  base := (-1952558921972316882087373430450029939583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-196868430176495165975988910333370500000000000)
      constant := (2269507084953916780017790912360199668298463553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree048.table
  base := (-78210182577934941570890333243532548879/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-473964715261208383020277920842216570500000000000)
      constant := (5478900823540958045916443802652725378912039277225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85654687411772509399/25000000000000000000)
  centralHi := (342618749647090037597/100000000000000000000)
  directionLo := (69248889170089341039/20000000000000000000)
  directionHi := (86561111462611676299/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree049.table
  base := (-697354778477231898736756313082102772601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-401945006903989516586078734298621000000000000)
      constant := (4735718655576284630432655327924691475062985955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree049.table
  base := (-3491743003301661412166535062119853485571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-403036515753856429436358111111371000000000000)
      constant := (4761605584286997874750930637819578298554262461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69248889170089341039/20000000000000000000)
  centralHi := (86561111462611676299/25000000000000000000)
  directionLo := (4372907087875554523/1250000000000000000)
  directionHi := (349832567030044361841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree050.table
  base := (-3047260854297828226626300121381198385517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-410153153454988701220179647930501000000000000)
      constant := (4936599464354090606524884449000474304390670547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree050.table
  base := (-305183900681429204860164593909190402753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-493725959063800904056417903936185200500000000000)
      constant := (5958753457688801894161918230927759915893466761115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4372907087875554523/1250000000000000000)
  centralHi := (349832567030044361841/100000000000000000000)
  directionLo := (17669212887631557023/5000000000000000000)
  directionHi := (353384257752631140461/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree051.table
  base := (-2586932943839881525063124309844699219211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-418361300005987885854280561562381000000000000)
      constant := (5141653263440217775454838915810012225046443701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree051.table
  base := (-1295574630011401951758483476164088924339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-503606580965097164574487895483169515500000000000)
      constant := (6206234707418052723035061755306870970883457331949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/5000000000000000000)
  centralHi := (353384257752631140461/100000000000000000000)
  directionLo := (356900605631211563437/100000000000000000000)
  directionHi := (178450302815605781719/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree052.table
  base := (-2106109901707086076641374639946466039073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-426569446556987070488381475194261000000000000)
      constant := (5350877044394469077458446971482755701038362143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree052.table
  base := (-527497881197171304647845603901808452347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-513487202866393425092557887030153830500000000000)
      constant := (6458747663843757066447341878518471788773505703754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356900605631211563437/100000000000000000000)
  centralHi := (178450302815605781719/50000000000000000000)
  directionLo := (360382645215433707893/100000000000000000000)
  directionHi := (180191322607716853947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree053.table
  base := (-1605080371500850762765382019582352806799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-434777593107986255122482388826141000000000000)
      constant := (5564268091369198856370575266506312642440828209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree053.table
  base := (-804326288773952167267140506838880150861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-523367824767689685610627878577138145500000000000)
      constant := (6716289087681391950044418167481734478461977791251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360382645215433707893/100000000000000000000)
  centralHi := (180191322607716853947/50000000000000000000)
  directionLo := (181915680773415410401/50000000000000000000)
  directionHi := (363831361546830820803/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree054.table
  base := (-1084104940274070771252256716756635525801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-442985739658985439756583302458021000000000000)
      constant := (5781823952500826421369052610369030816337738391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree054.table
  base := (-543695623205967798134667018505624126023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-533248446668985946128697870124122460500000000000)
      constant := (6978856055336859488861570740978617507068397272793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181915680773415410401/50000000000000000000)
  centralHi := (363831361546830820803/100000000000000000000)
  directionLo := (45905961676692979/12500000000000000)
  directionHi := (367247693413543832001/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree055.table
  base := (-543418877884497909376513394720440621011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-451193886209984624390684216089901000000000000)
      constant := (6003542414135260185699233094604380374196907501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree055.table
  base := (-273220573391004381102237999998702209571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-543129068570282206646767861671106775500000000000)
      constant := (7246445928006343822857168861866126627145261652861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45905961676692979/12500000000000000)
  centralHi := (367247693413543832001/100000000000000000000)
  directionLo := (185316268167500506767/50000000000000000000)
  directionHi := (74126507267000202707/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree056.table
  base := (2095674258870734729606348499267443133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-229701016380491904512392564860890500000000000)
      constant := (3114710738798847449480188260473866429489753588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree056.table
  base := (3496713420014432058423045897296010689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-11285912050440376880915058228940634500000000000)
      constant := (153450129057820856681030334328632997500128134498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185316268167500506767/50000000000000000000)
  centralHi := (74126507267000202707/20000000000000000000)
  directionLo := (186993372651722210291/50000000000000000000)
  directionHi := (373986745303444420583/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree057.table
  base := (7453200954184669848466229524001527427/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-233805089655991496829443021676830500000000000)
      constant := (3229729669124458150702930621174436714862425720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree057.table
  base := (593702413254247332568731781906407762947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1125780624745749455365815689530150811000000000000)
      constant := (15593370185623477935611812493699582836930405543523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/50000000000000000000)
  centralHi := (373986745303444420583/100000000000000000000)
  directionLo := (188655568653042261729/50000000000000000000)
  directionHi := (377311137306084523459/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree058.table
  base := (1194879984620588588268288497568506211329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-475818325862982178292986956985541000000000000)
      constant := (6693654366597974251660715486143140074942394561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree058.table
  base := (1192533713021755535660834173108642579423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1145541868548341976401955672624119441000000000000)
      constant := (16158660588321048505256092859378508407989528207807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188655568653042261729/50000000000000000000)
  centralHi := (377311137306084523459/100000000000000000000)
  directionLo := (380606493648963547301/100000000000000000000)
  directionHi := (190303246824481773651/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree059.table
  base := (1812480738929785434799406329338775645787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-484026472413981362927087870617421000000000000)
      constant := (6932005091265461682920363458860097540051209883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree059.table
  base := (452581412615744291874224204012966091219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-582651556175467248719047827859044035500000000000)
      constant := (8366990175918369670300800665808951474416846499942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380606493648963547301/100000000000000000000)
  centralHi := (190303246824481773651/50000000000000000000)
  directionLo := (383873562101255014149/100000000000000000000)
  directionHi := (7677471242025100283/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree060.table
  base := (244891712997014962397052458035785846701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-246117309482490273780594392124650500000000000)
      constant := (3587255091806574074460686231475823545158048545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree060.table
  base := (489387642033719146284687621805287562451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1185064356153527018474235638812056701000000000000)
      constant := (17319326313081178433988590637672209672854593015295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383873562101255014149/100000000000000000000)
  centralHi := (7677471242025100283/2000000000000000000)
  directionLo := (387113058876671907553/100000000000000000000)
  directionHi := (193556529438335953777/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree061.table
  base := (1552030822559279518929409686299184618907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-250221382757989866097644848940590500000000000)
      constant := (3710584221937381346828103324274714528079295963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree061.table
  base := (3102244994068816532832337541152095485961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1204825599956119539510375621906025331000000000000)
      constant := (17914695616594433470843016475607047860492204324649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387113058876671907553/100000000000000000000)
  centralHi := (193556529438335953777/50000000000000000000)
  directionLo := (97581417616714175943/25000000000000000000)
  directionHi := (390325670466856703773/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree062.table
  base := (472224892270853939270181846224808505079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-254325456033489458414695305756530500000000000)
      constant := (3835989394319816265579879316164577892897153244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree062.table
  base := (1888065947694493956131695943018454530533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-612293421879356030273257802499996980500000000000)
      constant := (9260042842294665667277074229596584210715361777797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97581417616714175943/25000000000000000000)
  centralHi := (390325670466856703773/100000000000000000000)
  directionLo := (39351205534004771129/10000000000000000000)
  directionHi := (393512055340047711291/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree063.table
  base := (4470025628689909681035014955862576019461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-516859058617978101463491525144941000000000000)
      constant := (7926940239555938296620353714877183977767108549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree063.table
  base := (4363765529438596730665536212860912897/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-12697429464911271240639342735652679500000000000)
      constant := (195260144795114435419098181490087987119188237824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39351205534004771129/10000000000000000000)
  centralHi := (393512055340047711291/100000000000000000000)
  directionLo := (396672845516927630917/100000000000000000000)
  directionHi := (198336422758463815459/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree064.table
  base := (5180647218302887020899519215630909307367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-525067205168977286097592438776821000000000000)
      constant := (8186051913133776404614081857644575225673016103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree064.table
  base := (2589622008712460862368018693852454961081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-632054665681948551309397785593965610500000000000)
      constant := (9880459515848000366868002435715537606697875520729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396672845516927630917/100000000000000000000)
  centralHi := (198336422758463815459/50000000000000000000)
  directionLo := (399808648034336413531/100000000000000000000)
  directionHi := (99952162008584103383/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree065.table
  base := (1477394778087263784754654625196863168623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-266637675859988235365846676204350500000000000)
      constant := (4224656505770110942927434376217862071107147614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree065.table
  base := (369268267811237716063072233024276904793/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-641935287583244811827467777140949925500000000000)
      constant := (10198179156628661117423871211889049264197366449096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399808648034336413531/100000000000000000000)
  centralHi := (99952162008584103383/25000000000000000000)
  directionLo := (80584009261289911323/20000000000000000000)
  directionHi := (50365005788306194577/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree066.table
  base := (1664186184175774997375989661322835332693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-270741749135487827682897133020290500000000000)
      constant := (4358361407144664830242475437451176115290616874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree066.table
  base := (3327782454899575436202326161449073011909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-651815909484541072345537768687934240500000000000)
      constant := (10520905161159706081078070606588229883203693326181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80584009261289911323/20000000000000000000)
  centralHi := (50365005788306194577/12500000000000000000)
  directionLo := (406007601392066323263/100000000000000000000)
  directionHi := (6343868771751036301/1562500000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree067.table
  base := (1855518735099300587149285218819261043427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-274845822410987419999947589836230500000000000)
      constant := (4494140335369821758713992725490579354315209286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree067.table
  base := (7420993464364861609118255502487247467299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1323393062771674665727215520469837111000000000000)
      constant := (21697273513035593217542759682119054744418978914691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406007601392066323263/100000000000000000000)
  centralHi := (6343868771751036301/1562500000000000000)
  directionLo := (25566990823487752411/6250000000000000000)
  directionHi := (409071853175804038577/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree068.table
  base := (410275363784821330040518715033473313171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-278949895686487012316998046652170500000000000)
      constant := (4631992996660212723738923928093713504036259390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree068.table
  base := (2051129043051443644655233899820419206327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-671577153287133593381677751781902870500000000000)
      constant := (11181373244906524706308094362308836803847812227886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25566990823487752411/6250000000000000000)
  centralHi := (409071853175804038577/100000000000000000000)
  directionLo := (82422664294048184457/20000000000000000000)
  directionHi := (206056660735120461143/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree069.table
  base := (562936584254687054443504831462452725617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-283053968961986604634048503468110500000000000)
      constant := (4771919125707791193895107697538371241562642824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree069.table
  base := (1801215452239837717073595496885612451141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1362915550376859707799495486657774371000000000000)
      constant := (23038227992703254855563566921293953673271191956345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82422664294048184457/20000000000000000000)
  centralHi := (206056660735120461143/50000000000000000000)
  directionLo := (207566253522689532099/50000000000000000000)
  directionHi := (415132507045379064199/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree070.table
  base := (614153639330433670969373523202214781637/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-287158042237486196951098960284050500000000000)
      constant := (4913918482920624038959098199086262111043380264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree070.table
  base := (9825626379810683405792034914818984249857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-28217893758764331200727254484729449000000000000)
      constant := (484157487432943720312336782470688551817538321137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207566253522689532099/50000000000000000000)
  centralHi := (415132507045379064199/100000000000000000000)
  directionLo := (418129892591200969279/100000000000000000000)
  directionHi := (1306655914347503029/312500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree071.table
  base := (10663879927392167607006295421883318371/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-291262115512985789268149417099990500000000000)
      constant := (5057990851929629074537138579158230571276369500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree071.table
  base := (1332889758766587634474112752246898514759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-701219018991022374935887726422855815500000000000)
      constant := (12209606068703006484351992778079999005026028807324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418129892591200969279/100000000000000000000)
  centralHi := (1306655914347503029/312500000000000000)
  directionLo := (105276485904639699149/25000000000000000000)
  directionHi := (421105943618558796597/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree072.table
  base := (11519208908199774816439265489580868734887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-590732377576970763170399747831861000000000000)
      constant := (10408272074674410379226465135309698393926551783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree072.table
  base := (5759255646092353345076120100824017768067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-711099640892318635453957717969840130500000000000)
      constant := (12562356412571998625946707466240097133814561509603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105276485904639699149/25000000000000000000)
  centralHi := (421105943618558796597/100000000000000000000)
  directionLo := (53007638662894671069/12500000000000000000)
  directionHi := (424061109303157368553/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree073.table
  base := (3098101915782939117194350437136365321597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-299470262063984973902250330731870500000000000)
      constant := (5352353862684247164863204544213223622621812346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree073.table
  base := (774485562155010846905254922826026609627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-720980262793614895972027709516824445500000000000)
      constant := (12920109055198864778425406360226430109578584349144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/12500000000000000000)
  centralHi := (424061109303157368553/100000000000000000000)
  directionLo := (106748955819240903523/25000000000000000000)
  directionHi := (426995823276963614093/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree074.table
  base := (13283442318997874842050398530326335054841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-607148670678969132438601575095621000000000000)
      constant := (11005288337228663053848090411632254486530998969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree074.table
  base := (13282857726354292234206973869674848613537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1461721769389822312980195402127617521000000000000)
      constant := (26565727237482940117927356719078027833602051888833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106748955819240903523/25000000000000000000)
  centralHi := (426995823276963614093/100000000000000000000)
  directionLo := (429910504370990570709/100000000000000000000)
  directionHi := (42991050437099057071/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree075.table
  base := (14192282285612032357920976449410062822893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-615356817229968317072702488727501000000000000)
      constant := (11310013622431855559476933643188824281100600237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree075.table
  base := (14191747287986670337827140695815278559053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1481483013192414834016335385221586151000000000000)
      constant := (27301239524155214651952187204060905232765073354477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429910504370990570709/100000000000000000000)
  centralHi := (42991050437099057071/10000000000000000000)
  directionLo := (432805557313058381493/100000000000000000000)
  directionHi := (216402778656529190747/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree076.table
  base := (15118899937576855854105118774597892066517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-623564963780967501706803402359381000000000000)
      constant := (11618883321050707962529008469672307566453858453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree076.table
  base := (7559205207225128472434636880984487557159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-750622128497503677526237684157777390500000000000)
      constant := (14023377177236170383663876150493682282764166983431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432805557313058381493/100000000000000000000)
  centralHi := (216402778656529190747/50000000000000000000)
  directionLo := (435681373383823495649/100000000000000000000)
  directionHi := (8713627467676469913/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree077.table
  base := (16063270326920655907503832781904473875251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-631773110331966686340904315991261000000000000)
      constant := (11931897198349754637222376468542726194692236659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree077.table
  base := (8031411245237829251448142890404872862131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-15520464293853059960087911749076769500000000000)
      constant := (293900726248474959764146977540975859489229738371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435681373383823495649/100000000000000000000)
  centralHi := (8713627467676469913/2000000000000000000)
  directionLo := (219269165517043335797/50000000000000000000)
  directionHi := (87707666206817334319/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree078.table
  base := (17025370923593386405728593174966735416189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-639981256882965870975005229623141000000000000)
      constant := (12249055042343754699685574005286600013530922301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree078.table
  base := (17024961292942815846137632224737072815609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1540766744600192397124755334503492041000000000000)
      constant := (29567789475747125255933686834787790185111078259481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219269165517043335797/50000000000000000000)
  centralHi := (87707666206817334319/20000000000000000000)
  directionLo := (220688398233068510567/50000000000000000000)
  directionHi := (88275359293227404227/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree079.table
  base := (3601036276223833423835637720704015946623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-648189403433965055609106143255021000000000000)
      constant := (12570356661592716592838283282309289430208879035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree079.table
  base := (1800480675840318396257019395155008462591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-780263994201392459080447658798730335500000000000)
      constant := (15171654405704265856533041007777150128617347221595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220688398233068510567/50000000000000000000)
  centralHi := (88275359293227404227/20000000000000000000)
  directionLo := (444197124181660260817/100000000000000000000)
  directionHi := (222098562090830130409/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree080.table
  base := (19002683324965467910843193514918259287857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-656397549984964240243207056886901000000000000)
      constant := (12895801883210663740621382614585945901639446513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree080.table
  base := (19002340773198234614634144555320801956853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1580289232205377439197035300691429301000000000000)
      constant := (31128828770128942593942121164940407814894483734677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444197124181660260817/100000000000000000000)
  centralHi := (222098562090830130409/50000000000000000000)
  directionLo := (446999657498531946783/100000000000000000000)
  directionHi := (13968739296829123337/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree081.table
  base := (4003572032285198019019443337766885580063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-664605696535963424877307970518781000000000000)
      constant := (13225390551067413578701813287124514132114063835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree081.table
  base := (20017546983977104408258924947693461805571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1600050476007969960233175283785397931000000000000)
      constant := (31924348982469661363468585735946036020890810711139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446999657498531946783/100000000000000000000)
  centralHi := (13968739296829123337/3125000000000000000)
  directionLo := (449784729038628465223/100000000000000000000)
  directionHi := (56223091129828558153/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree082.table
  base := (10525348452514068591954606491812594554703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-336406921543481304755704442075330500000000000)
      constant := (6779561262082327223361845598093635702165200527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree082.table
  base := (4210082125326013823589704404383710830097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1619811719810562481269315266879366561000000000000)
      constant := (32729869114894552364679777267012488733580593989365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449784729038628465223/100000000000000000000)
  centralHi := (56223091129828558153/12500000000000000000)
  directionLo := (452552661188617903559/100000000000000000000)
  directionHi := (11313816529715447589/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree083.table
  base := (4420236004533801873171671087007214067431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-681021989637961794145509797782541000000000000)
      constant := (13896997675169421160361357780867547385802291395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree083.table
  base := (5525229592961878953495524298199658452719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-819786481806577501152727624986667595500000000000)
      constant := (16772694433140531084046927963087011601054602006942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452552661188617903559/100000000000000000000)
  centralHi := (11313816529715447589/2500000000000000000)
  directionLo := (91060753307107568693/20000000000000000000)
  directionHi := (227651883267768921733/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree084.table
  base := (23169297292858122528916358211714210059619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-689230136188960978779610711414421000000000000)
      constant := (14239015889089709754604738899778143002450955171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree084.table
  base := (1448066136605516024460020079497792693181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-16931981708323954319812196255788814500000000000)
      constant := (350723550660921602936327437987165635228454891368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91060753307107568693/20000000000000000000)
  centralHi := (227651883267768921733/50000000000000000000)
  directionLo := (45803834827882600671/10000000000000000000)
  directionHi := (458038348278826006711/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree085.table
  base := (757969927456324360752198034639334351777/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-348719141369980081706855812523150500000000000)
      constant := (7292588531039226089283476162716161450653916688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree085.table
  base := (24254819203698224052093300907459561593027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1679095451218340044377735216161272451000000000000)
      constant := (35206426164923337520558485394094011958084127294243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/10000000000000000000)
  centralHi := (458038348278826006711/100000000000000000000)
  directionLo := (460756700620341138311/100000000000000000000)
  directionHi := (57594587577542642289/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree086.table
  base := (2535839121261086300618310855114966859057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-352823214645479674023906269339090500000000000)
      constant := (7467740550176704095191531148790596615884336565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree086.table
  base := (25358191617262479607266799090158394995521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1698856695020932565413875199255241081000000000000)
      constant := (36051943245153615097737831111728089201269369870689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460756700620341138311/100000000000000000000)
  centralHi := (57594587577542642289/12500000000000000000)
  directionLo := (463459109133794275837/100000000000000000000)
  directionHi := (231729554566897137919/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree087.table
  base := (6619837223406316367698334742153342611251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-356927287920979266340956726155030500000000000)
      constant := (7644963959610869187654066064326790101258521318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree087.table
  base := (6619791642750381056349645444703775934499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-859308969411762543225007591174604855500000000000)
      constant := (18453729502704595931390310721539283713690500638982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463459109133794275837/100000000000000000000)
  centralHi := (231729554566897137919/50000000000000000000)
  directionLo := (14567057847340734811/3125000000000000000)
  directionHi := (466145851114903513953/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree088.table
  base := (13808951296398784722422275612254156421221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-361031361196478858658007182970970500000000000)
      constant := (7824258721099555868374996712636823357767268389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree088.table
  base := (5523547214027703769188074767310432412631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1738379182626117607486155165443178341000000000000)
      constant := (37772973265079992291478458759593770220138193173395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14567057847340734811/3125000000000000000)
  centralHi := (466145851114903513953/100000000000000000000)
  directionLo := (18752687836539501441/4000000000000000000)
  directionHi := (234408597956743768013/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree089.table
  base := (14387022484570573503334481388728457472337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-365135434471978450975057639786910500000000000)
      constant := (8005624800107092546296837010754785556357218833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree089.table
  base := (1438694644843418224250753587897691741051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-879070213214355064261147574268573485500000000000)
      constant := (19324242930554258216220342280544459579013088104590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18752687836539501441/4000000000000000000)
  centralHi := (234408597956743768013/50000000000000000000)
  directionLo := (235736702624311831667/50000000000000000000)
  directionHi := (94294681049724732667/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree090.table
  base := (29947769393175861188843436470524317424849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-738479015494956086584216193205701000000000000)
      constant := (16378124330890179834112689619851753302650404241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree090.table
  base := (7486907633713449794596420652552805608713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-888950835115651324779217565815557800500000000000)
      constant := (19766998323142065276798931631042995997713371722834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235736702624311831667/50000000000000000000)
  centralHi := (94294681049724732667/20000000000000000000)
  directionLo := (14816085422122317967/3125000000000000000)
  directionHi := (94822946701582834989/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree091.table
  base := (6227813975594600890600554539589332088829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-746687162045955271218317106837581000000000000)
      constant := (16749141577896083752078562057209561128118960305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree091.table
  base := (31138943101058705858671639606540228255363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-36686998245589697359072961525001719000000000000)
      constant := (825091948728634954835831568813870369875080812883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14816085422122317967/3125000000000000000)
  centralHi := (94822946701582834989/20000000000000000000)
  directionLo := (29796339251989341811/6250000000000000000)
  directionHi := (476741428031829468977/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree092.table
  base := (3234794101688289367501329603762286460131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-377447654298477227926209010234730500000000000)
      constant := (8562150645180364988988158790768222766516862895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree092.table
  base := (16173912642102796845997430442456767335391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-908712078918243845815357548909526430500000000000)
      constant := (20667506132689172767794389069111045826484724099519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29796339251989341811/6250000000000000000)
  centralHi := (476741428031829468977/100000000000000000000)
  directionLo := (95870745876805526777/20000000000000000000)
  directionHi := (239676864692013816943/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree093.table
  base := (6714875585459491835896237915569096358361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-763103455147953640486518934101341000000000000)
      constant := (17503603422343659184230175769510151138179093245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree093.table
  base := (33574272289213518654707762680573915997179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1837185401639080212666855080913021491000000000000)
      constant := (42250516870984112037330238283455438214457514763611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95870745876805526777/20000000000000000000)
  centralHi := (239676864692013816943/50000000000000000000)
  directionLo := (240975935804243303429/50000000000000000000)
  directionHi := (481951871608486606859/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree094.table
  base := (17409188099931471192782785551339640892853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-385655800849476412560309923866610500000000000)
      constant := (8943523966178630928176502380180471681160853877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree094.table
  base := (34818279787035274090298731813660972430153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1856946645441672733702995064006990121000000000000)
      constant := (43176019206722867885178013545628942897618338294377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240975935804243303429/50000000000000000000)
  centralHi := (481951871608486606859/100000000000000000000)
  directionLo := (484536082474226804123/100000000000000000000)
  directionHi := (121134020618556701031/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree095.table
  base := (18039965926307253423383851906604984880111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-389759874124976004877360380682550500000000000)
      constant := (9137317391467615424109848969773918802736964399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree095.table
  base := (36079843869369164398666322177075324207471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1876707889244265254739135047100958751000000000000)
      constant := (44111519184302134299114951754824108650348895228239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484536082474226804123/100000000000000000000)
  centralHi := (121134020618556701031/25000000000000000000)
  directionLo := (60888322963543556861/12500000000000000000)
  directionHi := (487106583708348454889/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree096.table
  base := (3735904128955576152462608630789985197771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-393863947400475597194410837498490500000000000)
      constant := (9333181970121418058274685520191882853629136695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree096.table
  base := (72966720718304036453993828050146476953/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-948234566523428887887637515097463690500000000000)
      constant := (22528508362005405948484160141953682415113859987712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60888322963543556861/12500000000000000000)
  centralHi := (487106583708348454889/100000000000000000000)
  directionLo := (244831795609029221333/50000000000000000000)
  directionHi := (489663591218058442667/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree097.table
  base := (38655701263252426241969042460281862979437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (108)
      previous := (54)
      next := (54)
      square := (900213484426319876519073660000000000000)
      linear := (-84593053603140650337222084029000000000000)
      constant := (2025957633513122384860773276883281862979437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree097.table
  base := (38655628016743320031922171399543371780947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (259308)
      previous := (129654)
      next := (129654)
      square := (2161412576107594023522295857660000000000000)
      linear := (-203659302460351822384038156370379000000000000)
      constant := (4890265889455335709326344889928651635646053747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/50000000000000000000)
  centralHi := (489663591218058442667/100000000000000000000)
  directionLo := (98441463060463176369/20000000000000000000)
  directionHi := (246103657651157940923/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree098.table
  base := (39969908841051118811610576917822254946431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-804144187902949563657023502260741000000000000)
      constant := (19462249055788292383037399074708947596790969279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree098.table
  base := (39969842020401743048953830069542567688059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-806327205602683389357582255886241000000000000)
      constant := (19566015913767752983356059537308521519376947131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98441463060463176369/20000000000000000000)
  centralHi := (246103657651157940923/50000000000000000000)
  directionLo := (123684490213420899161/25000000000000000000)
  directionHi := (98947592170736719329/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree099.table
  base := (20650830687285972983746988532853608039879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-406176167226974374145562207946310500000000000)
      constant := (9933202480757100646228096684466714098047221511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree099.table
  base := (41301600422393200152213227079598012710471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1955752864454635338883694979476833271000000000000)
      constant := (47953494030569924961632548883524438948024364755239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123684490213420899161/25000000000000000000)
  centralHi := (98947592170736719329/20000000000000000000)
  directionLo := (15539241485966681877/3125000000000000000)
  directionHi := (99451145510186764013/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree100.table
  base := (42650956472157628371738657111752057954021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-820560481004947932925225329524501000000000000)
      constant := (20274703068399591906121280213149575113289383589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree100.table
  base := (42650900878728012712699369268893811861677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-1975514108257227859919834962570801901000000000000)
      constant := (48938981165772811909020659775173789248811451862093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15539241485966681877/3125000000000000000)
  centralHi := (99451145510186764013/20000000000000000000)
  directionLo := (249880405021460258457/50000000000000000000)
  directionHi := (99952162008584103383/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree101.table
  base := (11004447993498159493756383397066692827541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-414384313777973558779663121578190500000000000)
      constant := (10343571678061379960308308175504946525628666538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree101.table
  base := (11004435318313923035233141262642964855927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-997637676029910190477987472832385265500000000000)
      constant := (24967232783379530511061449303034937661193861120686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249880405021460258457/50000000000000000000)
  centralHi := (99952162008584103383/20000000000000000000)
  directionLo := (100450679624839501719/20000000000000000000)
  directionHi := (125563349531049377149/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree102.table
  base := (45402165929633593825775944226230231363251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-836976774106946302193427156788261000000000000)
      constant := (21103725806331983564568798149225162246896828659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree102.table
  base := (9080423939104656501487400243532972935733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2015036595862412901992114928758739161000000000000)
      constant := (50939947190369612379459873914771780241439503122985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100450679624839501719/20000000000000000000)
  centralHi := (125563349531049377149/25000000000000000000)
  directionLo := (504733676902830812379/100000000000000000000)
  directionHi := (25236683845141540619/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree103.table
  base := (5850509572214654871270611139741208102897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-422592460328972743413764035210070500000000000)
      constant := (10762225201227297976649643091831856608160631492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree103.table
  base := (4680403442078532687501144316898632882661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1017398919832502711514127455926353895500000000000)
      constant := (25977712998820362920327080087796494200449452974745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504733676902830812379/100000000000000000000)
  centralHi := (25236683845141540619/5000000000000000000)
  directionLo := (507201826960825099843/100000000000000000000)
  directionHi := (126800456740206274961/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree104.table
  base := (6027940290954370906198722754934425765561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-426696533604472335730814492026010500000000000)
      constant := (10974658564762280355730894360272484048112653796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree104.table
  base := (6027935486494546984350512846788306322077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1027279541733798972032197447473338210500000000000)
      constant := (26490450976698135002622491161608692593867193622772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507201826960825099843/100000000000000000000)
  centralHi := (126800456740206274961/25000000000000000000)
  directionLo := (254829012253778871009/50000000000000000000)
  directionHi := (509658024507557742019/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree105.table
  base := (9932100348596664034308715659807977552953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-861601213759943856095729897683901000000000000)
      constant := (22378325974026757698100306976363521303978673885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree105.table
  base := (6207558337914659304462194958690625400823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-21166533951736637398985049775924949500000000000)
      constant := (551187500264077865199472766062681623501683346972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254829012253778871009/50000000000000000000)
  centralHi := (509658024507557742019/100000000000000000000)
  directionLo := (256051220763294686947/50000000000000000000)
  directionHi := (102420488305317874779/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree106.table
  base := (12778753381654585836248549356351450732703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-434904680155471520364915405657890500000000000)
      constant := (11405738461878179723174810052982844599888005054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree106.table
  base := (10222996317160961110010453154637300661859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2094081571072782986136674861134613681000000000000)
      constant := (55061845186421389636575668328905136588438813128655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256051220763294686947/50000000000000000000)
  centralHi := (102420488305317874779/20000000000000000000)
  directionLo := (51453524591619712449/10000000000000000000)
  directionHi := (514535245916197124491/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree107.table
  base := (13146764126789592836361241041709851575767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-439008753430971112681965862473830500000000000)
      constant := (11624384983845917933115319445953954486952783406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree107.table
  base := (5258702739373083041738603458365886828359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1056921407437687753586407422114291155500000000000)
      constant := (28058656204569647745746025903953174375412198121155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51453524591619712449/10000000000000000000)
  centralHi := (514535245916197124491/100000000000000000000)
  directionLo := (51695660162395548087/10000000000000000000)
  directionHi := (516956601623955480871/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree108.table
  base := (27038314813397436397408716985456796707401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-443112826706470704999016319289770500000000000)
      constant := (11845102547940133243003511624698197000219936009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree108.table
  base := (54076603092792015485628071371798011187941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2133604058677968028208954827322550941000000000000)
      constant := (57182776670667392437292648218783188959928875822469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51695660162395548087/10000000000000000000)
  centralHi := (516956601623955480871/100000000000000000000)
  directionLo := (8115104199619844653/1562500000000000000)
  directionHi := (519366668775670057793/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree109.table
  base := (11116746386056918115037359798620131153011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-894433799963940594632133552211421000000000000)
      constant := (24135782299333767499456218661421983070093402495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree109.table
  base := (13895926937311183800512088853573472601431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1076682651240280274622547405208259785500000000000)
      constant := (29129118974955734912711551844402586777900362267758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8115104199619844653/1562500000000000000)
  centralHi := (519366668775670057793/100000000000000000000)
  directionLo := (521765603798951212749/100000000000000000000)
  directionHi := (2087062415195804851/400000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree110.table
  base := (57108362555008496923813849127910856263419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-902641946514939779266234465843301000000000000)
      constant := (24585501569935956474358611900102123246582509371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree110.table
  base := (11421668104026385177178310185998824127269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2173126546283153070281234793510488201000000000000)
      constant := (59343696227828277043657901300542266971742755622105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521765603798951212749/100000000000000000000)
  centralHi := (2087062415195804851/400000000000000000)
  directionLo := (104830711908339474571/20000000000000000000)
  directionHi := (65519194942712171607/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree111.table
  base := (11730104144398835489209805502356095002317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-910850093065938963900335379475181000000000000)
      constant := (25039362900357481963674945284907543489384003265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree111.table
  base := (58650500644459668511742259929419970510809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2192887790085745591317374776604456831000000000000)
      constant := (60439151487226193618348610569275573282089420716281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104830711908339474571/20000000000000000000)
  centralHi := (65519194942712171607/12500000000000000000)
  directionLo := (52653068538574202827/10000000000000000000)
  directionHi := (526530685385742028271/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree112.table
  base := (3763137857988017325892795929199076501007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-459529119808469074267218146553530500000000000)
      constant := (12748683141989869765445679457118008886383798904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree112.table
  base := (12042037487046242285452264026929220752933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-45156102732415063517418668565273989000000000000)
      constant := (1256012320665005505100948420590449402325764916265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52653068538574202827/10000000000000000000)
  centralHi := (526530685385742028271/100000000000000000000)
  directionLo := (52889712735590350789/10000000000000000000)
  directionHi := (528897127355903507891/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree113.table
  base := (3089370846861734514668367633877922844413/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-463633193083968666584268603369470500000000000)
      constant := (12979755857412990417631996195732585260430819170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree113.table
  base := (15446850068063778004293192727403654350451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1116205138845465316694827371396197045500000000000)
      constant := (31330026444947377488303402327649389728127855390118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52889712735590350789/10000000000000000000)
  centralHi := (528897127355903507891/100000000000000000000)
  directionLo := (531253028224662805637/100000000000000000000)
  directionHi := (265626514112331402819/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree114.table
  base := (12676430755332469068928407154266511576963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-935474532718936517802638120370821000000000000)
      constant := (26425799187499099306567442278375722037138224335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree114.table
  base := (31691069297826136433020456207247389744089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1126085760746761577212897362943181360500000000000)
      constant := (31892749503253207784852811037186467442685222295801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531253028224662805637/100000000000000000000)
  centralHi := (265626514112331402819/50000000000000000000)
  directionLo := (533598527612681795379/100000000000000000000)
  directionHi := (26679926380634089769/5000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree115.table
  base := (32497207864056909695405690684706893898001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-471841339634967851218369517001350500000000000)
      constant := (13448114348562722686004158656109589664686291409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree115.table
  base := (32497200949996978874283392817322525875613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1135966382648057837730967354490165675500000000000)
      constant := (32460471025501053200159285027682044439208706163517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533598527612681795379/100000000000000000000)
  centralHi := (26679926380634089769/5000000000000000000)
  directionLo := (133983440521340522787/25000000000000000000)
  directionHi := (535933762085362091149/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree116.table
  base := (33312101161926338057356855623796521634611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-475945412910467443535419973817290500000000000)
      constant := (13685400119652043451139221631291979472060054899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree116.table
  base := (8328023716126184030168385170511697041881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1145847004549354098249037346037149990500000000000)
      constant := (33033191006537106052145147314685174170413628191716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133983440521340522787/25000000000000000000)
  centralHi := (535933762085362091149/100000000000000000000)
  directionLo := (6728235815570418927/1250000000000000000)
  directionHi := (538258865245633514161/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree117.table
  base := (17067878285378360880489129927165161480649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-480049486185967035852470430633230500000000000)
      constant := (13924756905030493585691290521682507508742852882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree117.table
  base := (68271501670808151928049120387161499499259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2311455252901300717534214675168268611000000000000)
      constant := (67221818883417706974775444493236199346641255562331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6728235815570418927/1250000000000000000)
  centralHi := (538258865245633514161/100000000000000000000)
  directionLo := (540573967823150561839/100000000000000000000)
  directionHi := (6757174597789382023/1250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree118.table
  base := (69936347799703581008326271880563722947557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-968307118922933256339041774898341000000000000)
      constant := (28332369405807623764775685504951202069213563813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree118.table
  base := (1748408433839142009423286252612947061541/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1165608248351946619285177329131118620500000000000)
      constant := (34193626326816352266422850302808541631925925697380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540573967823150561839/100000000000000000000)
  centralHi := (6757174597789382023/1250000000000000000)
  directionLo := (8482487465001021619/1562500000000000000)
  directionHi := (542879197760065383617/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree119.table
  base := (17904676488507923590146575225586993635017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-488257632736966220486571344265110500000000000)
      constant := (14409683511651809027152706424423900546223749906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree119.table
  base := (71618696441629615566051739024153135750831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (49792428)
      previous := (24896214)
      next := (24896214)
      square := (415035325073394942190230239280060000000000000)
      linear := (-47979137561356852236867237578698079000000000000)
      constant := (1419646598288499539590028276699918939359698875071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8482487465001021619/1562500000000000000)
  centralHi := (542879197760065383617/100000000000000000000)
  directionLo := (109034936058707301041/20000000000000000000)
  directionHi := (272587340146768252603/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree120.table
  base := (73318587293520690028430449223498145881629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-984723412024931625607243602162101000000000000)
      constant := (29310506659622986566756932438662014054600247261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree120.table
  base := (2291205582250105875332982990928215214341/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1185369492154539140321317312225087250500000000000)
      constant := (35374055432042013733886642184401671587177831361104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109034936058707301041/20000000000000000000)
  centralHi := (272587340146768252603/50000000000000000000)
  directionLo := (547460538035123862679/100000000000000000000)
  directionHi := (13686513450878096567/2500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree121.table
  base := (75035991537368563233868987159595367283597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-992931558575930810241344515793981000000000000)
      constant := (29805788312123663239174138907793143810771364173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree121.table
  base := (37517991825585996183293021841030307761949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1195250114055835400839387303772071565500000000000)
      constant := (35971767645648187334533254086155262494922959716541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547460538035123862679/100000000000000000000)
  centralHi := (13686513450878096567/2500000000000000000)
  directionLo := (274868445523606284303/50000000000000000000)
  directionHi := (549736891047212568607/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree122.table
  base := (1199545600500361402541361742024499428981/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-500569852563464997437722714712930500000000000)
      constant := (15152605989209987785142554594547063484073031328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree122.table
  base := (76770911252236168144381114911690678726281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2410261471914263322714914590638111761000000000000)
      constant := (73148956592195815627980267755680841497821522607529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274868445523606284303/50000000000000000000)
  centralHi := (549736891047212568607/100000000000000000000)
  directionLo := (552003856916600197057/100000000000000000000)
  directionHi := (276001928458300098529/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree123.table
  base := (39261683874270138103221291711345380795001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-504673925838964589754773171528870500000000000)
      constant := (15404388828178894198515469104351515187900164409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree123.table
  base := (78523361212325091749176031090458040246613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2430022715716855843751054573732080391000000000000)
      constant := (74364374761747473562845563721113469321833596502517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552003856916600197057/100000000000000000000)
  centralHi := (276001928458300098529/50000000000000000000)
  directionLo := (22170462033015008289/4000000000000000000)
  directionHi := (277130775412687603613/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree124.table
  base := (80293339280198251947111391617029432394399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-1017555998228928364143647256689621000000000000)
      constant := (31316485343992056767845510092983593929398900191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree124.table
  base := (80293333330260515107618734084180601765281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2449783959519448364787194556826049021000000000000)
      constant := (75589789795406528860833067063130577471104878958529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22170462033015008289/4000000000000000000)
  centralHi := (277130775412687603613/50000000000000000000)
  directionLo := (22260403424768295781/4000000000000000000)
  directionHi := (278255042809603697263/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree125.table
  base := (20520208210085797239339904335102311787989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-512882072389963774388874085160750500000000000)
      constant := (15914167519783277219230007992112392803226377002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree125.table
  base := (82080827424447916121498852636342674574373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2469545203322040885823334539920017651000000000000)
      constant := (76825201689070578038871408400782878713393731612357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22260403424768295781/4000000000000000000)
  centralHi := (278255042809603697263/50000000000000000000)
  directionLo := (558749571873164933479/100000000000000000000)
  directionHi := (13968739296829123337/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree126.table
  base := (41942924130221720113321927440489081988519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-516986145665463366705924541976690500000000000)
      constant := (16172163370747783571076126489041894772429975271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree126.table
  base := (41942921665486300302479888528362931133791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (24896214)
      previous := (12448107)
      next := (12448107)
      square := (207517662536697471095115119640030000000000000)
      linear := (-25401086195149320478157903296061084500000000000)
      constant := (796638882030985946585465850937236347382854136431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558749571873164933479/100000000000000000000)
  centralHi := (13968739296829123337/2500000000000000000)
  directionLo := (560980117955166630873/100000000000000000000)
  directionHi := (280490058977583315437/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree127.table
  base := (85708385388332499314090263931772388234849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8470108674967243718167964066940000000000000)
      linear := (-1042180437881925918045949997585261000000000000)
      constant := (32864460448347360219820039111112383400901694241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree127.table
  base := (42854190450940419525696904605045826924607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1254533845463612963947807253053977455500000000000)
      constant := (39663008020981119502739230984143485521216239058463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560980117955166630873/100000000000000000000)
  centralHi := (280490058977583315437/50000000000000000000)
  directionLo := (70400228760896551889/12500000000000000000)
  directionHi := (563201830087172415113/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree128.table
  base := (10943555510827778095696073679505351270427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-525194292216462551340025455608570500000000000)
      constant := (16694368079414624324260731406740807400413790572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree128.table
  base := (43774220001814028478849651966851259389567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (1219914486)
      previous := (609957243)
      next := (609957243)
      square := (10168365464298176083660640862361470000000000000)
      linear := (-1264414467364909224465877244600961770500000000000)
      constant := (40295709247415260037339547168155047846531042603103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell047.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70400228760896551889/12500000000000000000)
  centralHi := (563201830087172415113/100000000000000000000)
  directionLo := (17669212887631557023/3125000000000000000)
  directionHi := (565414812404209824737/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree129.table
  base := (44703012115634932152496446493009267848113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4235054337483621859083982033470000000000000)
      linear := (-529298365491962143657075912424510500000000000)
      constant := (16958576935887057086045415745356383701182895217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree129.table
  base := (89406020515677844749160800212577966784047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2439828972)
      previous := (1219914486)
      next := (1219914486)
      square := (20336730928596352167321281724722940000000000000)
      linear := (-2548590178532410969967894472295892171000000000000)
      constant := (81866817794918426859447467343689962604820106833423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell047.Kernel129
